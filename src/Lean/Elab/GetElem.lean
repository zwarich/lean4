/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Lean.Elab.Term
import Lean.Parser.Term

namespace Lean.Elab.Term

@[builtin_term_elab getElem] def elabGetElem : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]) => elabTerm (← `(getElem $xs $i (by get_elem_tactic))) expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem'] def elabGetElem' : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]'$h) => elabTerm (← `(getElem $xs $i $h)) expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem?] def elabGetElem? : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]?) => elabTerm (← `(getElem? $xs $i)) expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab getElem!] def elabGetElem! : TermElab := fun stx expectedType? => do
  match stx with
  | `($xs[$i]!) => elabTerm (← `(getElem! $xs $i)) expectedType?
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
