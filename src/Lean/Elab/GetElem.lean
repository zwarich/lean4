/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Lean.Elab.Term
import Lean.Parser.Term

namespace Lean.Elab.Term

def elabNonDependentIfPossible (dependent : Expr) (elabNonDependent : TermElabM Expr) :
    TermElabM Expr := do
  let dependent ← instantiateMVars dependent
  dbg_trace "{dependent}"
  match (dependent.getArg! 4).getAppFn with
  | .const name _ =>
      if name = `GetElem.toDGetElem then elabNonDependent
      else return dependent
  | _ => return dependent

@[builtin_term_elab getElem] def elabGetElem : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]) =>
      let dependent ← elabTerm (← `(DGetElem.getElem $xs $i (by get_elem_tactic))) expectedType?
      elabNonDependentIfPossible dependent
        (elabTerm (← `(GetElem.getElem $xs $i (by get_elem_tactic))) expectedType?)
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem'] def elabGetElem' : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]'$h) =>
      let dependent ← elabTerm (← `(DGetElem.getElem $xs $i $h)) expectedType?
      elabNonDependentIfPossible dependent
        (elabTerm (← `(GetElem.getElem $xs $i $h)) expectedType?)
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem?] def elabGetElem? : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]?) =>
      let dependent ← elabTerm (← `(DGetElem.getElem? $xs $i)) expectedType?
      elabNonDependentIfPossible dependent
        (elabTerm (← `(GetElem.getElem? $xs $i)) expectedType?)
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem!] def elabGetElem! : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]!) =>
      let dependent ← elabTerm (← `(DGetElem.getElem! $xs $i)) expectedType?
      elabNonDependentIfPossible dependent
        (elabTerm (← `(GetElem.getElem! $xs $i)) expectedType?)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
