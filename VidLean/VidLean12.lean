import Mathlib
import VidLean10
import VidLean11

-- VIDLEAN BUILD VidLean12-v2-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean12

open VidLean8 VidLean9 VidLean10 VidLean11

def E := Fin 2 → ℝ

def e1 : E := fun i => if i = 0 then 1 else 0
def e2 : E := fun i => if i = 1 then 1 else 0

instance : AddCommGroup E := Pi.addCommGroup
instance : Module ℝ E := Pi.instModule
instance : TopologicalSpace E := Pi.topologicalSpace
instance : TopologicalAddGroup E := Pi.topologicalAddGroup

noncomputable instance : InnerProductSpace ℝ E where
  inner x y := Finset.sum Finset.univ (fun i : Fin 2 => x i * y i)
  inner_add_left := by intros; simp [Finset.sum_add_distrib, add_mul]
  inner_smul_left := by intros; simp [Finset.mul_sum, mul_assoc]
  inner_comm := by intros; simp [mul_comm]
  inner_self_nonneg := by intros; apply Finset.sum_nonneg; intros; exact mul_self_nonneg _
  inner_self_eq_zero := by
    intro x
    constructor
    · intro h
      funext i
      have : x i ^ 2 = 0 := by
        have h' : ∑ j : Fin 2, x j ^ 2 = 0 := by
          simpa using h
        have : x i ^ 2 ≥ 0 := sq_nonneg (x i)
        have h2 : ∀ j, x j ^ 2 ≥ 0 := fun j => sq_nonneg (x j)
        have h3 : x i ^ 2 ≤ ∑ j : Fin 2, x j ^ 2 := by
          fin_cases i <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        linarith
      rw [pow_eq_zero_iff two_ne_zero] at this
      exact this
    · intro h
      rw [h]
      simp
  norm_sq_eq_inner := by intro x; simp [norm_eq_sqrt_real_inner, Real.sq_sqrt]
  conj_symm := by intros; simp
  add_left := by intros; simp [Finset.sum_add_distrib]
  smul_left := by intros; simp [Finset.mul_sum]

theorem inner_e1_e2 : @inner ℝ _ _ e1 e2 = 0 := by
  simp [e1, e2]

theorem inner_e1_e1 : @inner ℝ _ _ e1 e1 = 1 := by
  simp [e1, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem inner_e2_e2 : @inner ℝ _ _ e2 e2 = 1 := by
  simp [e2, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

def testSigma (x : E) : Fin 3 :=
  if x = e1 then 0 else if x = e2 then 1 else 2

def testS : SelectionOperator where
  potential := E
  poset := Fin 3
  sigma := testSigma

theorem sharing_0_1 : BandRel testS 0 1 := by
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · unfold testSigma
    split_ifs with h1 h2
    · rfl
    · contradiction
    · contradiction
  · unfold testSigma
    split_ifs with h1 h2
    · contradiction
    · rfl
    · contradiction
  · rw [Shares]
    rw [inner_e1_e2]
    norm_num

theorem sharing_1_2 : BandRel testS 1 2 := by
  refine ⟨e2, e1 + e2, ?_, ?_, ?_⟩
  · unfold testSigma
    split_ifs with h1 h2
    · have : e2 = e1 := by
        have h3 : e2 0 = (e1 + e2) 0 := by rw [h1]
        simp [e1, e2] at h3
      contradiction
    · rfl
    · contradiction
  · unfold testSigma
    split_ifs with h1 h2
    · have : e1 + e2 = e1 := by
        have h3 : (e1 + e2) 1 = e1 1 := by rw [h1]
        simp [e1, e2] at h3
      have : e2 = 0 := by
        ext i
        fin_cases i
        · simp [e1, e2] at this ⊢
        · simp [e1, e2] at this ⊢
          linarith
      contradiction
    · have : e1 + e2 = e2 := by
        have h3 : (e1 + e2) 0 = e2 0 := by rw [h2]
        simp [e1, e2] at h3
      have : e1 = 0 := by
        ext i
        fin_cases i
        · simp [e1, e2] at this ⊢
          linarith
        · simp [e1, e2] at this ⊢
      contradiction
    · rfl
  · rw [Shares]
    have h : @inner ℝ _ _ e2 (e1 + e2)
        = @inner ℝ _ _ e2 e1 + @inner ℝ _ _ e2 e2 := by
      rw [inner_add_right]
    rw [h, inner_e2_e2, inner_e1_e2]
    norm_num

theorem not_sharing_0_2 : ¬ BandRel testS 0 2 := by
  intro h
  rcases h with ⟨x, y, hx, hy, hsh⟩
  unfold testSigma at hx hy
  split_ifs at hx hy
  · rw [hx] at hsh
    rw [Shares] at hsh
    simp [e1] at hsh
  · rw [hx] at hsh
    rw [Shares] at hsh
    simp [e1] at hsh
  · rw [hx] at hsh
    rw [Shares] at hsh
    simp [e1] at hsh
  · rw [hy] at hsh
    rw [Shares] at hsh
    simp [e2] at hsh
  · rw [hy] at hsh
    rw [Shares] at hsh
    simp [e2] at hsh
  · rw [hy] at hsh
    rw [Shares] at hsh
    simp [e2] at hsh

end VidLean12
