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
  elabTerm (← `(getElem $(⟨stx[0]⟩) $(⟨stx[2]⟩) (by get_elem_tactic))) expectedType?

@[builtin_term_elab getElem'] def elabGetElem' : TermElab := fun stx expectedType? => do
  elabTerm (← `(getElem $(⟨stx[0]⟩) $(⟨stx[2]⟩) $(⟨stx[4]⟩))) expectedType?

@[builtin_term_elab getElem?] def elabGetElem? : TermElab := fun stx expectedType? => do
  elabTerm (← `(getElem? $(⟨stx[0]⟩) $(⟨stx[2]⟩))) expectedType?

@[builtin_term_elab getElem!] def elabGetElem! : TermElab := fun stx expectedType? => do
  elabTerm (← `(getElem! $(⟨stx[0]⟩) $(⟨stx[2]⟩))) expectedType?

end Lean.Elab.Term
