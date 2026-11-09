import Mathlib

-- VIDLEAN BUILD VidLean7-v3-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean7

structure SelectionOperator where
  potential : Type
  [potential_normed : NormedAddCommGroup potential]
  [potential_inner : InnerProductSpace ℝ potential]
  [potential_csmul : ContinuousSMul ℝ potential]
  poset     : Type
  [poset_order : PartialOrder poset]
  sigma     : potential → poset

attribute [instance] SelectionOperator.potential_normed
attribute [instance] SelectionOperator.potential_inner
attribute [instance] SelectionOperator.potential_csmul
attribute [instance] SelectionOperator.poset_order

def BandRel (S : SelectionOperator) (A B : S.poset) : Prop :=
  ∃ x y : S.potential, S.sigma x = A ∧ S.sigma y = B ∧
    @inner ℝ _ _ x y ≠ 0

def Shares (S : SelectionOperator) (x y : S.potential) : Prop :=
  @inner ℝ _ _ x y ≠ 0

def H (S : SelectionOperator) (A : S.poset) : Submodule ℝ S.potential :=
  Submodule.span ℝ (S.sigma ⁻¹' {A})

theorem sharing_refl (S : SelectionOperator) (x : S.potential)
    (hx : x ≠ 0) : Shares S x x := by
  rw [Shares, real_inner_self_eq_norm_sq]
  have h : ‖x‖ ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    rw [norm_ne_zero_iff]
    exact hx
  exact h

theorem sharing_symm (S : SelectionOperator) (x y : S.potential)
    (h : Shares S x y) : Shares S y x := by
  rw [Shares, real_inner_comm]
  exact h

def Band (S : SelectionOperator) (A B : S.poset) : Prop :=
  Relation.TransGen (BandRel S) A B

theorem band_trans (S : SelectionOperator) {A B C : S.poset}
    (hAB : BandRel S A B) (hBC : BandRel S B C) : BandRel S A C := by
  obtain ⟨x1, y1, hσ1, hτ1, hsh1⟩ := hAB
  obtain ⟨x2, y2, hσ2, hτ2, hsh2⟩ := hBC
  rw [hτ1] at hσ2
  exact ⟨x1, y2, hσ1, hτ2, hsh1⟩

theorem band_symm (S : SelectionOperator) (A B : S.poset)
    (h : Band S A B) : Band S B A := by
  induction h using Relation.TransGen.head_induction_on with
  | single hstep => exact Relation.TransGen.single (sharing_symm S _ _ hstep)
  | tail h1 h2 ih => exact Relation.TransGen.trans ih (Relation.TransGen.single h2)

end VidLean7
