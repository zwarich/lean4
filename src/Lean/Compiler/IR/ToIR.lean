/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
prelude
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.CtorLayout
import Lean.CoreM
import Lean.Environment

namespace Lean.IR

open Lean.Compiler (LCNF.AltCore LCNF.Arg LCNF.Code LCNF.Decl LCNF.LCtx LCNF.LetDecl LCNF.LetValue LCNF.LitValue LCNF.Param LCNF.getMonoDecl?)

namespace ToIR

inductive FVarClassification where
  | var (id : VarId)
  | joinPoint (id : JoinPointId)
  | erased

structure BuilderState where
  fvars : Std.HashMap FVarId FVarClassification := {}
  nextVarId : Nat := 1
  nextJoinPointId : Nat := 1

abbrev M := StateT BuilderState CoreM

def M.run (x : M α) : CoreM α := do
  x.run' {}

def bindVar (fvarId : FVarId) : M VarId := do
  modifyGet fun s =>
    let varId := { idx := s.nextVarId }
    ⟨varId, { s with fvars := s.fvars.insertIfNew fvarId (.var varId),
                     nextVarId := s.nextVarId + 1 }⟩

def bindJoinPoint (fvarId : FVarId) : M JoinPointId := do
  modifyGet fun s =>
    let joinPointId := { idx := s.nextJoinPointId }
    ⟨joinPointId, { s with fvars := s.fvars.insertIfNew fvarId (.joinPoint joinPointId),
                           nextJoinPointId := s.nextJoinPointId + 1 }⟩

def bindErased (fvarId : FVarId) : M Unit := do
  modify fun s => { s with fvars := s.fvars.insertIfNew fvarId .erased }

def findDecl (n : Name) : M (Option Decl) :=
  return findEnvDecl (← Lean.getEnv) n

def addDecl (d : Decl) : M Unit :=
  Lean.modifyEnv fun env => declMapExt.addEntry (env.addExtraName d.name) d

def visitLitValue (v : LCNF.LitValue) : LitVal :=
  match v with
  | .natVal n => .num n
  | .strVal s => .str s

def visitType (e : Lean.Expr) : M IRType := do
  match e with
  | .const name .. =>
    match name with
    | ``UInt8 => return .uint8
    | ``UInt16 => return .uint16
    | ``UInt32 => return .uint32
    | ``USize => return .usize
    | ``Float => return .float
    | ``Float32 => return .float32
    | _ => return .object
  | .app (.const ``lcErased ..) .. => return .irrelevant
  | .app .. | .forallE .. => return .object
  | _ => panic! "invalid type"

-- TODO: This should be cached.
def getCtorInfo (name: Name) : M CtorInfo := do
  match getCtorLayout (← Lean.getEnv) name with
  | .ok ctorLayout =>
    return {
      name,
      cidx := ctorLayout.cidx,
      size := ctorLayout.numObjs,
      usize := ctorLayout.numUSize,
      ssize := ctorLayout.scalarSize
    }
  | .error .. => panic! "unrecognized constructor"

def visitArg (a : LCNF.Arg) : M Arg := do
  match a with
  | .fvar fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) => return .var varId
    | some .erased => return .irrelevant
    | some (.joinPoint ..) => panic! "join point used as arg"
    | none => panic! "unbound fvar arg"
  | .erased | .type .. => return .irrelevant

inductive TranslatedLetValue where
  | expr (e : Expr)
  | erased
  deriving Inhabited

def visitLetValue (v : LCNF.LetValue) : M TranslatedLetValue := do
  match v with
  | .value litValue =>
    return .expr (.lit (visitLitValue litValue))
  | .proj _ i fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) => return .expr (.proj i varId)
    | some .erased => return .erased
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | none => panic! "reference to unbound variable"
  | .const name _us args =>
    let irArgs ← args.mapM visitArg
    match (← Lean.getEnv).find? name with
    | some (.ctorInfo ..) =>
      return .expr (.ctor (← getCtorInfo name) irArgs)
    | some (.defnInfo ..) | some (.opaqueInfo ..) =>
      if let some decl ← LCNF.getMonoDecl? name then
        let numArgs := irArgs.size
        let numParams := decl.params.size
        if numArgs < numParams then
          return .expr (.pap name irArgs)
        else if numArgs == numParams then
          return .expr (.fap name irArgs)
        else
          panic! "more args than params"
      -- TODO: This shouldn't be required, but is a temporary hack to get more stuff working.
      else if let some decl := IR.findEnvDecl (← Lean.getEnv) name then
        let numArgs := irArgs.size
        let numParams := decl.params.size
        if numArgs < numParams then
          return .expr (.pap name irArgs)
        else if numArgs == numParams then
          return .expr (.fap name irArgs)
        else
          panic! "more args than params"
      else
        panic! "definition without an LCNF or IR decl"
    | some (.quotInfo ..) => panic! "quot unsupported by code generator"
    | some (.inductInfo ..) => panic! "induct unsupported by code generator"
    | some (.axiomInfo ..) => panic! "axiom unsupported by code generator"
    | some (.recInfo ..) => panic! "rec unsupported by code generator"
    | some (.thmInfo ..) => panic! "thm unsupported by code generator"
    | none => IO.println f!"unbound name: {name}"; panic! "reference to unbound name"
  | .fvar fvarId args =>
    let irArgs ← args.mapM visitArg
    match (← get).fvars[fvarId]? with
    | some (.var id) => return .expr (.ap id irArgs)
    | some .erased => return .erased
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | .none => panic! "reference to unbound variable"
  | .erased => return .erased

def visitParam (p : LCNF.Param) : M Param := do
  let x ← bindVar p.fvarId
  let ty ← visitType p.type
  return { x, borrow := p.borrow, ty }

mutual
partial def visitCode (c : LCNF.Code) : M FnBody := do
  match c with
  | .let decl k =>
    let var ← bindVar decl.fvarId
    let type ← visitType decl.type
    match (← visitLetValue decl.value) with
    | .expr e => return .vdecl var type e (← visitCode k)
    | .erased => visitCode k
  | .jp decl k =>
    let joinPoint ← bindJoinPoint decl.fvarId
    let params ← decl.params.mapM visitParam
    let body ← visitCode decl.value
    return .jdecl joinPoint params body (← visitCode k)
  | .jmp fvarId args =>
    match (← get).fvars[fvarId]? with
    | some (.joinPoint joinPointId) =>
      return .jmp joinPointId (← args.mapM visitArg)
    | some (.var ..) | some .erased => panic! "expected join point"
    | none => panic! "reference to unbound variable"
  | .cases cases =>
    match (← get).fvars[cases.discr]? with
    | some (.var varId) =>
      return .case cases.typeName
                  varId
                  (← visitType cases.resultType)
                  (← cases.alts.mapM visitAlt)
    | some (.joinPoint ..) | some .erased => panic! "expected var"
    | none => panic! "reference to unbound variable"
  | .return fvarId =>
    let arg := match (← get).fvars[fvarId]? with
    | some (.var varId) => .var varId
    | some .erased => .irrelevant
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | none => panic! "reference to unbound variable"
    return .ret arg
  | .unreach .. => return .unreachable
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def visitAlt (a : LCNF.AltCore LCNF.Code) : M (AltCore FnBody) := do
  match a with
  | .alt ctorName params code =>
    params.forM fun param => bindVar param.fvarId |> discard
    return .ctor (← getCtorInfo ctorName) (← visitCode code)
  | .default code =>
    return .default (← visitCode code)
end

def visitDecl (d : LCNF.Decl) : M Decl := do
  let params ← d.params.mapM visitParam
  let type ← visitType d.type
  let body ← visitCode d.value
  let decl := .fdecl d.name params type body {}
  addDecl decl
  return decl

end ToIR

def toIR (decls: Array LCNF.Decl) : CoreM (Array Decl) :=
  decls.mapM ToIR.visitDecl |>.run

end Lean.IR
