/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ForEachExprWhere
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF
namespace Closure

/-!
# Dependency collector for code specialization and lambda lifting.

During code specialization and lambda lifting, we have code `C` containing free variables. These free variables
are in a scope, and we say we are computing `C`'s closure.
This module is used to compute the closure.
-/

structure Context where
  /--
  `inScope x` returns `true` if `x` is a variable that is not in `C`.
  -/
  inScope : FVarId → Bool
  /--
  If `abstract x` returns `true`, we convert `x` into a closure parameter. Otherwise,
  we collect the dependencies in the `let`/`fun`-declaration too, and include the declaration in the closure.
  Remark: the lambda lifting pass abstracts all `let`/`fun`-declarations.
  -/
  abstract : FVarId → Bool
  /--
  Indicates whether we are processing terms beneath a binder.
  -/
  isUnderBinder : Bool

inductive Value where
  | nonAbstract (decl : CodeDecl)
  | abstract (param : Param)
  deriving Inhabited

/--
State for the `ClosureM` monad.
-/
structure State where
  /--
  Values of already visited free variables.
  -/
  values : Std.HashMap FVarId Value := {}

/--
Monad for implementing the dependency collector.
-/
abbrev ClosureM := ReaderT Context $ StateRefT State CompilerM

mutual
 /--
  Collect dependencies in parameters. We need this because parameters may
  contain other type parameters.
  -/
  partial def collectParams (params : Array Param) : ClosureM Unit :=
    params.forM (collectType ·.type)

  partial def collectArg (arg : Arg) : ClosureM Unit :=
    match arg with
    | .erased => return ()
    | .type e => collectType e
    | .fvar fvarId => collectFVar fvarId

  partial def collectLetValue (e : LetValue) : ClosureM Unit := do
    match e with
    | .erased | .value .. => return ()
    | .proj _ _ fvarId => collectFVar fvarId
    | .const _ _ args => args.forM collectArg
    | .fvar fvarId args => collectFVar fvarId; args.forM collectArg

  /--
  Collect dependencies in the given code. We need this function to be able
  to collect dependencies in a local function declaration.
  -/
  partial def collectCode (c : Code) : ClosureM Unit := do
    match c with
    | .let decl k =>
      collectType decl.type
      withReader (fun ctx => { ctx with isUnderBinder := ctx.isUnderBinder || decl.type.isForall })
        do collectLetValue decl.value
      collectCode k
    | .fun decl k | .jp decl k => collectFunDecl decl; collectCode k
    | .cases c =>
      collectType c.resultType
      collectFVar c.discr
      c.alts.forM fun alt => do
        match alt with
        | .default k => collectCode k
        | .alt _ ps k => collectParams ps; collectCode k
    | .jmp _ args => args.forM collectArg
    | .unreach type => collectType type
    | .return fvarId => collectFVar fvarId

  /-- Collect dependencies of a local function declaration. -/
  partial def collectFunDecl (decl : FunDecl) : ClosureM Unit := do
    collectType decl.type
    collectParams decl.params
    withReader (fun ctx => { ctx with isUnderBinder := true }) do
      collectCode decl.value

  /--
  Process the given free variable.
  If it has not already been visited and is in scope, we collect its dependencies.
  -/
  partial def collectFVar (fvarId : FVarId) : ClosureM Unit := do
    let processFvar (_ : Unit) : ClosureM Unit := do
      let ctx ← read
      if ctx.inScope fvarId then
        /- We only collect the variables in the scope of the function application being specialized. -/
        let value ← if let some funDecl ← findFunDecl? fvarId then
          if ctx.isUnderBinder || ctx.abstract funDecl.fvarId then
            pure <| .abstract { funDecl with borrow := false }
          else
            collectFunDecl funDecl
            pure <| .nonAbstract (.fun funDecl)
        else if let some param ← findParam? fvarId then
          collectType param.type
          pure <| .abstract param
        else if let some letDecl ← findLetDecl? fvarId then
          collectType letDecl.type
          if ctx.isUnderBinder || ctx.abstract letDecl.fvarId then
            pure <| .abstract { letDecl with borrow := false }
          else
            collectLetValue letDecl.value
            pure <| .nonAbstract (.let letDecl)
        else
          unreachable!
        modify fun s => { s with values := s.values.insert fvarId value }
    match (← get).values.get? fvarId with
    | none => processFvar ()
    | some (.nonAbstract _) =>
      if (← read).isUnderBinder then
        processFvar ()
    | some (.abstract _) => return ()

  /-- Collect dependencies of the given expression. -/
  partial def collectType (type : Expr) : ClosureM Unit := do
    type.forEachWhere Expr.isFVar fun e => collectFVar e.fvarId!

end

def run (x : ClosureM α) (inScope : FVarId → Bool) (abstract : FVarId → Bool := fun _ => true) : CompilerM (α × Array Param × Array CodeDecl) := do
  let (a, s) ← x { inScope, abstract, isUnderBinder := false } |>.run {}
  let mut params := #[]
  let mut decls := #[]
  for ⟨_, value⟩ in s.values do
    match value with
    | .nonAbstract decl => decls := decls.push decl
    | .abstract param => params := params.push param
  return (a, params, decls)

end Closure

end Lean.Compiler.LCNF
