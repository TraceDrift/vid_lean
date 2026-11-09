import Mathlib
import VidLean8

-- VIDLEAN BUILD VidLean9-v3-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean9

open VidLean8

def SpanPair (S : SelectionOperator) (A B : S.poset) : Submodule ℝ S.potential :=
  H S A ⊔ H S B

theorem cross_band_finite_span_orthogonal (S : SelectionOperator) (A B : S.poset)
    (hAB : ¬ BandRel S A B) :
    Submodule.IsOrtho (H S A) (H S B) := by
  rw [Submodule.isOrtho_iff_le]
  intro u hu
  rw [Submodule.mem_orthogonal']
  intro w hw
  exact cross_band_orthogonal S A B hAB u hu w hw

end VidLean9
