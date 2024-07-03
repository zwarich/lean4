/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.ForEachExpr

namespace Lean.Elab.Structural

/--
Information about the argument of interest of a structurally recursive function.

The `Expr`s in this data structure expect the `fixedParams` to be in scope, but not the other
parameters of the function. This ensures that this data structure makes sense in the other functions
of a mutually recursive group.
-/
structure RecArgInfo where
  /-- the name of the recursive function -/
  fnName      : Name
  /-- the fixed prefix of arguments of the function we are trying to justify termination using structural recursion. -/
  numFixed    : Nat
  /-- position of the argument (counted including fixed prefix) we are recursing on -/
  recArgPos   : Nat
  /-- position of the indices (counted including fixed prefix) of the inductive datatype indices we are recursing on -/
  indicesPos  : Array Nat
  /-- inductive datatype name of the argument we are recursing on -/
  indName     : Name
  /-- inductive datatype universe levels of the argument we are recursing on -/
  indLevels   : List Level
  /-- inductive datatype parameters of the argument we are recursing on -/
  indParams   : Array Expr
  /-- The types mutually inductive with indName -/
  indAll      : Array Name
deriving Inhabited
/--
If `xs` are the parameters of the functions (excluding fixed prefix), partitions them
into indices and major arguments, and other parameters.
-/
def RecArgInfo.pickIndicesMajor (info : RecArgInfo) (xs : Array Expr) : (Array Expr × Array Expr) := Id.run do
  let mut indexMajorArgs := #[]
  let mut otherArgs := #[]
  for h : i in [:xs.size] do
    let j := i + info.numFixed
    if j = info.recArgPos || info.indicesPos.contains j then
      indexMajorArgs := indexMajorArgs.push xs[i]
    else
      otherArgs := otherArgs.push xs[i]
  return (indexMajorArgs, otherArgs)

structure State where
  /-- As part of the inductive predicates case, we keep adding more and more discriminants from the
     local context and build up a bigger matcher application until we reach a fixed point.
     As a side-effect, this creates matchers. Here we capture all these side-effects, because
     the construction rolls back any changes done to the environment and the side-effects
     need to be replayed. -/
  addMatchers : Array (MetaM Unit) := #[]

abbrev M := StateRefT State MetaM

instance : Inhabited (M α) where
  default := throwError "failed"

def run (x : M α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run x s

/--
  Return true iff `e` contains an application `recFnName .. t ..` where the term `t` is
  the argument we are trying to recurse on, and it contains loose bound variables.

  We use this test to decide whether we should process a matcher-application as a regular
  application or not. That is, whether we should push the `below` argument should be affected by the matcher or not.
  If `e` does not contain an application of the form `recFnName .. t ..`, then we know
  the recursion doesn't depend on any pattern variable in this matcher.
-/
def recArgHasLooseBVarsAt (recFnName : Name) (recArgPos : Nat) (e : Expr) : Bool :=
  let app?   := e.find? fun e =>
     e.isAppOf recFnName && e.getAppNumArgs > recArgPos && (e.getArg! recArgPos).hasLooseBVars
  app?.isSome

end Lean.Elab.Structural
