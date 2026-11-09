import Mathlib
import VidLean14

-- VIDLEAN BUILD VidLean15-a4a-v7-20261110

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean15

open VidLean8 VidLean9 VidLean12 VidLean14

def BandEq (S : SelectionOperator) (A B : S.poset) : Prop :=
  Band S A B ∨ A = B

theorem bandEq_refl (S : SelectionOperator) (A : S.poset) :
    BandEq S A A := Or.inr rfl

theorem bandEq_symm (S : SelectionOperator) {A B : S.poset}
    (h : BandEq S A B) : BandEq S B A := by
  rcases h with h | rfl
  · exact Or.inl (band_symm S A B h)
  · exact Or.inr rfl

theorem bandEq_trans (S : SelectionOperator) {A B C : S.poset}
    (h1 : BandEq S A B) (h2 : BandEq S B C) : BandEq S A C := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (Relation.TransGen.trans h1 h2)
    · exact Or.inl h1
  · exact h2

def bandSpace (S : SelectionOperator) (A : S.poset) :
    Submodule ℝ S.potential :=
  (⨆ C : {C : S.poset // BandEq S A C}, H S C.1).topologicalClosure

theorem refl_le (S : SelectionOperator) (A : S.poset) :
    H S A ≤ bandSpace S A := by
  apply le_trans (b := ⨆ C : {C : S.poset // BandEq S A C}, H S C.1)
  · intro x hx
    rw [Submodule.mem_iSup]
    intro N hN
    exact hN (⟨A, bandEq_refl S A⟩ : {C : S.poset // BandEq S A C}) hx
  · exact Submodule.le_topologicalClosure _

theorem isOrtho_topologicalClosure_right (S : SelectionOperator)
    (U Y : Submodule ℝ S.potential)
    (h : Submodule.IsOrtho U Y) :
    Submodule.IsOrtho U Y.topologicalClosure := by
  intro u hu
  rw [Submodule.mem_orthogonal']
  intro z hz
  by_contra hne
  have hpos : 0 < |@inner ℝ _ _ u z| := abs_pos.mpr hne
  obtain ⟨y, hy_mem, hy_dist⟩ :=
    (Metric.mem_closure_iff).mp hz
      (|@inner ℝ _ _ u z| / (2 * (‖u‖ + 1)))
      (div_pos hpos (by positivity))
  have huy : ∀ v ∈ Y, @inner ℝ _ _ u v = 0 :=
    (Submodule.mem_orthogonal' Y u).mp (h hu)
  have hzero : @inner ℝ _ _ u y = 0 := huy y hy_mem
  have hcalc : |@inner ℝ _ _ u z| = |@inner ℝ _ _ u (z - y)| := by
    have hs : @inner ℝ _ _ u z - @inner ℝ _ _ u y
        = @inner ℝ _ _ u (z - y) := by
      rw [inner_sub_right]
    rw [hzero] at hs
    rw [sub_zero] at hs
    rw [hs]
  have hbound : |@inner ℝ _ _ u (z - y)| ≤ ‖u‖ * dist z y := by
    rw [dist_eq_norm]
    exact abs_inner_le S u (z - y)
  have hnum : dist z y * (2 * (‖u‖ + 1)) < |@inner ℝ _ _ u z| :=
    (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (‖u‖ + 1))).mp hy_dist
  have hcontra : |@inner ℝ _ _ u z| < |@inner ℝ _ _ u z| := by
    calc |@inner ℝ _ _ u z| = |@inner ℝ _ _ u (z - y)| := hcalc
      _ ≤ ‖u‖ * dist z y := hbound
      _ ≤ (‖u‖ + 1) * dist z y :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)) dist_nonneg
      _ = dist z y * (‖u‖ + 1) := mul_comm _ _
      _ ≤ dist z y * (2 * (‖u‖ + 1)) :=
        mul_le_mul_of_nonneg_left
          (by rw [two_mul]; exact le_add_of_nonneg_right (by positivity))
          dist_nonneg
      _ < |@inner ℝ _ _ u z| := hnum
  exact (lt_irrefl _ hcontra)

theorem bandSpace_isOrtho (S : SelectionOperator) {A B : S.poset}
    (hAB : ¬ BandEq S A B) :
    Submodule.IsOrtho (bandSpace S A) (bandSpace S B) := by
  rw [@Submodule.isOrtho_iff_le ℝ S.potential _ _ _
      (bandSpace S A) (bandSpace S B)]
  apply Submodule.topologicalClosure_minimal
  · intro x hx
    refine (Submodule.mem_iSup
        (fun C : {C : S.poset // BandEq S A C} => H S C.1)).mp hx
      (Submodule.orthogonal (bandSpace S B)) ?_
    intro C
    apply Submodule.isOrtho_iff_le.mpr
    apply isOrtho_topologicalClosure_right
    rw [@Submodule.isOrtho_iff_le ℝ S.potential _ _ _ (H S C.1)
        (⨆ D : {D : S.poset // BandEq S B D}, H S D.1),
      ← @Submodule.iInf_orthogonal ℝ S.potential _ _ _ _
        (fun D : {D : S.poset // BandEq S B D} => H S D.1)]
    apply le_iInf
    intro D
    apply Submodule.isOrtho_iff_le.mpr
    exact cross_band_isOrtho S C.1 D.1 (fun hrel => hAB
      (bandEq_trans S
        (bandEq_trans S C.2 (Or.inl (Relation.TransGen.single hrel)))
        (bandEq_symm S D.2)))
  · exact Submodule.isClosed_orthogonal _

theorem bandSpace_coverage (S : SelectionOperator) :
    ⨆ A : S.poset, bandSpace S A = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_iSup]
  intro N hN
  exact hN (S.sigma x) (refl_le S (S.sigma x)
    (Submodule.le_topologicalClosure _
      (Submodule.subset_span rfl)))

end VidLean15
