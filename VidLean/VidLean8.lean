import Mathlib
import VidLean7

-- VIDLEAN BUILD VidLean8-v3-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean8

structure SelectionOperator where
  potential : Type
  [potential_normed : NormedAddCommGroup potential]
  [potential_inner : InnerProductSpace ℝ potential]
  [potential_csmul : ContinuousSMul ℝ potential]
  [potential_complete : CompleteSpace potential]
  poset     : Type
  [poset_order : PartialOrder poset]
  sigma     : potential → poset

attribute [instance] SelectionOperator.potential_normed
attribute [instance] SelectionOperator.potential_inner
attribute [instance] SelectionOperator.potential_csmul
attribute [instance] SelectionOperator.potential_complete
attribute [instance] SelectionOperator.poset_order

def Shares (S : SelectionOperator) (x y : S.potential) : Prop :=
  @inner ℝ _ _ x y ≠ 0

def BandRel (S : SelectionOperator) (A B : S.poset) : Prop :=
  ∃ x y : S.potential, S.sigma x = A ∧ S.sigma y = B ∧ Shares S x y

def H (S : SelectionOperator) (A : S.poset) : Submodule ℝ S.potential :=
  (Submodule.span ℝ (S.sigma ⁻¹' {A})).topologicalClosure

theorem abs_inner_le (S : SelectionOperator) (x y : S.potential) :
    |@inner ℝ _ _ x y| ≤ ‖x‖ * ‖y‖ := by
  have h := inner_mul_inner_self_le (𝕜 := ℝ) x y
  rw [real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq y] at h
  change ‖@inner ℝ _ _ x y‖ * ‖@inner ℝ _ _ y x‖ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 at h
  have hcomm : ‖@inner ℝ _ _ y x‖ = ‖@inner ℝ _ _ x y‖ := by
    rw [real_inner_comm]
  rw [hcomm, Real.norm_eq_abs] at h
  nlinarith [abs_nonneg (@inner ℝ _ _ x y),
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem span_pair_zero (S : SelectionOperator) (A B : S.poset)
    (hAB : ¬ BandRel S A B) (u' v' : S.potential)
    (hu' : u' ∈ Submodule.span ℝ (S.sigma ⁻¹' {A}))
    (hv' : v' ∈ Submodule.span ℝ (S.sigma ⁻¹' {B})) :
    @inner ℝ _ _ u' v' = 0 := by
  let K : Submodule ℝ S.potential :=
    { carrier := {x | ∀ y ∈ S.sigma ⁻¹' {B}, @inner ℝ _ _ x y = 0},
      zero_mem' := by intro y hy; simp
      add_mem' := by
        intro a b ha hb y hy
        rw [inner_add_left, ha y hy, hb y hy, add_zero]
      smul_mem' := by
        intro r a ha y hy
        rw [inner_smul_left, ha y hy, mul_zero] }
  have hu'K : u' ∈ K :=
    (Submodule.mem_span.1 hu') K (by
      intro x hx y hy
      by_contra h
      exact hAB ⟨x, y, hx, hy, h⟩)
  let K2 : Submodule ℝ S.potential :=
    { carrier := {v | @inner ℝ _ _ u' v = 0},
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        have ha' : @inner ℝ _ _ u' a = 0 := ha
        have hb' : @inner ℝ _ _ u' b = 0 := hb
        show @inner ℝ _ _ u' (a + b) = 0
        rw [inner_add_right, ha', hb', add_zero]
      smul_mem' := by
        intro r a ha
        have ha' : @inner ℝ _ _ u' a = 0 := ha
        show @inner ℝ _ _ u' (r • a) = 0
        rw [inner_smul_right, ha', mul_zero] }
  exact (Submodule.mem_span.1 hv') K2 (by
    intro y hy
    exact hu'K y hy)

theorem cross_band_orthogonal (S : SelectionOperator) (A B : S.poset)
    (hAB : ¬ BandRel S A B) : Submodule.IsOrtho (H S A) (H S B) := by
  intro u hu
  rw [Submodule.mem_orthogonal']
  intro w hw
  by_contra hne
  have hpos : 0 < |@inner ℝ _ _ u w| := abs_pos.mpr hne
  set i := |@inner ℝ _ _ u w| with hi
  obtain ⟨y, hy_mem, hy_dist⟩ :=
    (Metric.mem_closure_iff).mp hw
      (i / (2 * (‖u‖ + i + 1)))
      (div_pos hpos (by positivity))
  obtain ⟨u', hu'_mem, hu'_dist⟩ :=
    (Metric.mem_closure_iff).mp hu
      (i / (2 * (‖w‖ + 1)))
      (div_pos hpos (by positivity))
  have hyz := span_pair_zero S A B hAB u' y hu'_mem hy_mem
  have e1 : @inner ℝ _ _ u w
      = @inner ℝ _ _ (u - u') w + @inner ℝ _ _ u' w := by
    rw [← inner_add_left, sub_add_cancel]
  have e2 : @inner ℝ _ _ u' w
      = @inner ℝ _ _ u' (w - y) + @inner ℝ _ _ u' y := by
    rw [← inner_add_right, sub_add_cancel]
  have hcs1 : |@inner ℝ _ _ (u - u') w| ≤ ‖u - u'‖ * ‖w‖ :=
    abs_inner_le S (u - u') w
  have hcs2 : |@inner ℝ _ _ u' (w - y)| ≤ ‖u'‖ * ‖w - y‖ :=
    abs_inner_le S u' (w - y)
  have hchain : |@inner ℝ _ _ u w|
      ≤ ‖u - u'‖ * ‖w‖ + ‖u'‖ * ‖w - y‖ := by
    calc |@inner ℝ _ _ u w|
        = |@inner ℝ _ _ (u - u') w + @inner ℝ _ _ u' (w - y)| := by
          rw [e1, e2, hyz, add_zero]
      _ ≤ |@inner ℝ _ _ (u - u') w| + |@inner ℝ _ _ u' (w - y)| := by
          apply abs_le.2
          constructor
          · have h1 := (abs_le.1
              (le_refl |@inner ℝ _ _ (u - u') w|)).1
            have h2 := (abs_le.1
              (le_refl |@inner ℝ _ _ u' (w - y)|)).1
            linarith
          · have h1 := le_abs_self (@inner ℝ _ _ (u - u') w)
            have h2 := le_abs_self (@inner ℝ _ _ u' (w - y))
            linarith
      _ ≤ ‖u - u'‖ * ‖w‖ + ‖u'‖ * ‖w - y‖ := add_le_add hcs1 hcs2
  have hd1 : ‖u - u'‖ = dist u u' := (dist_eq_norm u u').symm
  have hd2 : ‖w - y‖ = dist w y := (dist_eq_norm w y).symm
  have hb1 : dist u u' * ‖w‖ < i / 2 := by
    have h2w1 : (0:ℝ) < 2 * (‖w‖ + 1) := by positivity
    have hd2' : dist u u' * (2 * (‖w‖ + 1)) < i :=
      (lt_div_iff₀ h2w1).mp hu'_dist
    have hstep2 : (dist u u' * (‖w‖ + 1)) * 2 < i := by
      calc (dist u u' * (‖w‖ + 1)) * 2
          = dist u u' * (2 * (‖w‖ + 1)) := by ring
        _ < i := hd2'
    have hstep : dist u u' * (‖w‖ + 1) < i / 2 :=
      (lt_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr hstep2
    calc dist u u' * ‖w‖ ≤ dist u u' * (‖w‖ + 1) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)) dist_nonneg
      _ < i / 2 := hstep
  have hb1' : ‖u - u'‖ * ‖w‖ < i / 2 := by
    rw [hd1]; exact hb1
  have hu'C : ‖u'‖ < ‖u‖ + i := by
    have hD1 : 1 ≤ ‖w‖ + 1 := by
      have := norm_nonneg w
      linarith
    have hdiv : (i / 2) / (‖w‖ + 1) ≤ i / 2 :=
      div_le_self (by positivity) hD1
    have hf : i / (2 * (‖w‖ + 1)) ≤ i / 2 := by
      have e : i / (2 * (‖w‖ + 1)) = (i / 2) / (‖w‖ + 1) := by
        rw [← div_div]
      rw [e]; exact hdiv
    calc ‖u'‖ = ‖(u' - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖u' - u‖ + ‖u‖ := norm_add_le _ _
      _ = dist u u' + ‖u‖ := by rw [norm_sub_rev u' u, dist_eq_norm]
      _ < i / (2 * (‖w‖ + 1)) + ‖u‖ :=
          add_lt_add_left hu'_dist ‖u‖
      _ ≤ i / 2 + ‖u‖ := by linarith [hf]
      _ = ‖u‖ + i / 2 := add_comm _ _
      _ < ‖u‖ + i := by linarith [half_lt_self hpos]
  have hb2 : ‖u'‖ * ‖w - y‖ < i / 2 := by
    rw [hd2]
    have hK : 0 < ‖u‖ + i :=
      add_pos_of_nonneg_of_pos (norm_nonneg u) hpos
    have h2C : (0:ℝ) < 2 * (‖u‖ + i + 1) := by positivity
    have hy' : dist w y * (2 * (‖u‖ + i + 1)) < i :=
      (lt_div_iff₀ h2C).mp hy_dist
    have hK2 : (‖u‖ + i) * 2 ≤ 2 * (‖u‖ + i + 1) := by
      have h1 : ‖u‖ + i ≤ ‖u‖ + i + 1 :=
        le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)
      calc (‖u‖ + i) * 2 ≤ (‖u‖ + i + 1) * 2 :=
            mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ = 2 * (‖u‖ + i + 1) := mul_comm _ _
    have hcd2 : ((‖u‖ + i) * dist w y) * 2 < i := by
      calc ((‖u‖ + i) * dist w y) * 2
          = dist w y * ((‖u‖ + i) * 2) := by ring
        _ ≤ dist w y * (2 * (‖u‖ + i + 1)) :=
            mul_le_mul_of_nonneg_left hK2 dist_nonneg
        _ < i := hy'
    have hcd : (‖u‖ + i) * dist w y < i / 2 :=
      (lt_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr hcd2
    calc ‖u'‖ * dist w y
        ≤ (‖u‖ + i) * dist w y :=
          mul_le_mul_of_nonneg_right hu'C.le dist_nonneg
      _ < i / 2 := hcd
  have hhalf : i / 2 + i / 2 = i := by ring
  have hlt : i < i :=
    lt_of_le_of_lt hchain (by rw [← hhalf]; exact add_lt_add hb1' hb2)
  exact (lt_irrefl _ hlt)

def Band (S : SelectionOperator) (A B : S.poset) : Prop :=
  Relation.TransGen (BandRel S) A B

theorem sharing_symm (S : SelectionOperator) {A B : S.poset}
    (h : BandRel S A B) : BandRel S B A := by
  obtain ⟨x, y, hx, hy, hinner⟩ := h
  exact ⟨y, x, hy, hx, by rw [real_inner_comm]; exact hinner⟩

theorem band_symm (S : SelectionOperator) {A B : S.poset}
    (h : Band S A B) : Band S B A := by
  induction h with
  | single hstep => exact Relation.TransGen.single (sharing_symm S hstep)
  | tail h1 h2 ih => exact Relation.TransGen.head (sharing_symm S h2) ih

theorem cross_band_finite_span_orthogonal (S : SelectionOperator) (A B : S.poset)
    (hAB : ¬ BandRel S A B) :
    Submodule.IsOrtho (H S A) (H S B) := by
  rw [Submodule.isOrtho_iff_le]
  intro u hu
  rw [Submodule.mem_orthogonal']
  intro w hw
  exact cross_band_orthogonal S A B hAB u hu w hw

end VidLean8
