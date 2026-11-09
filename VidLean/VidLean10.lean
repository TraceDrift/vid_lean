import Mathlib
import VidLean9

-- VIDLEAN BUILD VidLean10-v3-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean10

open VidLean8 VidLean9

def IsLocallyConstantAt (S : SelectionOperator) (ψ : S.potential) : Prop :=
  ∃ ε > 0, ∀ ψ', dist ψ ψ' < ε → S.sigma ψ' = S.sigma ψ

theorem no_singular_of_locally_constant (S : SelectionOperator) (ψ : S.potential)
    (h : IsLocallyConstantAt S ψ) : ¬ VidLean8.IsSingular S ψ := by
  rcases h with ⟨ε, hε, hconst⟩
  intro hs
  rcases hs with ⟨A, hA, hA'⟩
  obtain ⟨ψ', hψ'1, hψ'2⟩ := hA' ε hε
  have hσ : S.sigma ψ' = S.sigma ψ := hconst ψ' hψ'1
  have hAψ : A ≤ S.sigma ψ := hA
  rw [hσ] at hAψ
  exact hψ'2 hAψ

def IsConstant (S : SelectionOperator) : Prop :=
  ∀ ψ ψ', S.sigma ψ = S.sigma ψ'

theorem no_singular_of_constant (S : SelectionOperator)
    (h : IsConstant S) : ∀ ψ, ¬ VidLean8.IsSingular S ψ := by
  intro ψ
  have hloc : IsLocallyConstantAt S ψ := by
    use 1
    constructor
    · norm_num
    · intro ψ' _
      exact h ψ ψ'
  exact no_singular_of_locally_constant S ψ hloc

end VidLean10
