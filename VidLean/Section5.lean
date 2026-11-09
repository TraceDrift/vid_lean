import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Set.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Order.UpperLowerSet
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.MetricSpace.PseudoDef
import Mathlib.Topology.UnitInterval

-- VIDLEAN BUILD Section5-7.1-v17-20261110

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLeanSection5

structure SelectionOperator where
  potential : Type
  [potential_normed : NormedAddCommGroup potential]
  [potential_module : Module ℝ potential]
  [potential_csmul : ContinuousSMul ℝ potential]
  [potential_inner : InnerProductSpace ℝ potential]
  poset     : Type
  [poset_order : PartialOrder poset]
  [poset_topology : TopologicalSpace poset]
  poset_opens_are_upper : ∀ U : Set poset, @IsOpen poset poset_topology U → IsUpperSet U
  sigma     : potential → poset

attribute [instance] SelectionOperator.potential_normed
attribute [instance] SelectionOperator.potential_module
attribute [instance] SelectionOperator.potential_csmul
attribute [instance] SelectionOperator.potential_inner
attribute [instance] SelectionOperator.poset_order
attribute [instance] SelectionOperator.poset_topology

@[reducible]
def upsetTopology (L : Type*) [PartialOrder L] : TopologicalSpace L where
  IsOpen U := IsUpperSet U
  isOpen_univ := by simp [IsUpperSet]
  isOpen_inter := by
    intro U V hU hV
    exact IsUpperSet.inter hU hV
  isOpen_sUnion := by
    intro S h x hx y hxy
    obtain ⟨U, hU, hxU⟩ := hx
    exact ⟨U, hU, h U hU x hxU y hxy⟩

def OrderContinuous (S : SelectionOperator) (ψ : S.potential) : Prop :=
  ∀ A : S.poset, A ≤ S.sigma ψ →
    ∃ ε > 0, ∀ ψ', dist ψ ψ' < ε → A ≤ S.sigma ψ'

def IsSingular (S : SelectionOperator) (ψ : S.potential) : Prop :=
  ∃ A : S.poset, A ≤ S.sigma ψ ∧
    ∀ ε > 0, ∃ ψ', dist ψ ψ' < ε ∧ ¬ A ≤ S.sigma ψ'

theorem orderContinuous_implies_open (S : SelectionOperator)
    (h : ∀ ψ, OrderContinuous S ψ) (A : S.poset) :
    @IsOpen S.potential (UniformSpace.toTopologicalSpace) (S.sigma ⁻¹' {B | A ≤ B}) := by
  rw [isOpen_iff_nhds]
  intro ψ hψ
  rw [Metric.mem_nhds_iff]
  obtain ⟨ε, hε, hε'⟩ := h ψ A hψ
  exact ⟨ε, hε, fun ψ' hψ' => hε' ψ' hψ'⟩

theorem open_implies_orderContinuous (S : SelectionOperator)
    (h : ∀ A, @IsOpen S.potential (UniformSpace.toTopologicalSpace)
      (S.sigma ⁻¹' {B | A ≤ B})) (ψ : S.potential) :
    OrderContinuous S ψ := by
  intro A hA
  have hopen : @IsOpen S.potential (UniformSpace.toTopologicalSpace)
    (S.sigma ⁻¹' {B | A ≤ B}) := h A
  rw [isOpen_iff_nhds] at hopen
  have hn := hopen ψ hA
  rw [Metric.mem_nhds_iff] at hn
  obtain ⟨ε, hε, hε'⟩ := hn
  exact ⟨ε, hε, hε'⟩

theorem orderContinuous_iff_open (S : SelectionOperator) :
    (∀ ψ, OrderContinuous S ψ) ↔
    (∀ A, @IsOpen S.potential (UniformSpace.toTopologicalSpace)
      (S.sigma ⁻¹' {B | A ≤ B})) :=
  ⟨orderContinuous_implies_open S, open_implies_orderContinuous S⟩

theorem sigma_continuous_of_orderContinuous (S : SelectionOperator)
    (h : ∀ ψ, OrderContinuous S ψ) :
    @Continuous S.potential S.poset
      (UniformSpace.toTopologicalSpace) S.poset_topology S.sigma := by
  rw [continuous_def]
  intro U hU
  have hup : IsUpperSet U := S.poset_opens_are_upper U hU
  rw [isOpen_iff_generateFrom_iff]
  intro V hV
  obtain ⟨A, rfl⟩ := hV
  exact orderContinuous_implies_open S h A

theorem isPathConnected_univ_potential (S : SelectionOperator) :
    @IsPathConnected S.potential (UniformSpace.toTopologicalSpace) Set.univ := by
  intro x _y hx hy
  use fun t => (1 - (t : ℝ)) • x + (t : ℝ) • _y
  constructor
  · fun_prop
  · constructor
    · simp
    · constructor
      · simp
      · rfl

theorem isConnected_image_of_continuous {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} (hs : IsConnected s) {f : α → β} (hf : Continuous f) :
    IsConnected (f '' s) := by
  constructor
  · obtain ⟨x, hx⟩ := hs.1
    exact ⟨f x, mem_image_of_mem f hx⟩
  · rw [isPreconnected_iff_subset_or_subset]
    intro U V hU hV hUV hsub
    have hpre : s ⊆ f ⁻¹' U ∪ f ⁻¹' V := by
      intro x hx
      have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
      have hfx' : f x ∈ U ∪ V := hUV hfx
      simpa using hfx'
    have hprecon := hs.2 (f ⁻¹' U) (f ⁻¹' V)
      (continuous_def.mp hf U hU)
      (continuous_def.mp hf V hV) hpre
    rcases hprecon with hsubU | hsubV
    · left
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hsubU hx
    · right
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hsubV hx

theorem singularity_exists (S : SelectionOperator)
    (surj : Function.Surjective S.sigma)
    (disconnected : ¬ IsConnected (Set.univ : Set S.poset)) :
    ∃ ψ : S.potential, IsSingular S ψ := by
  by_contra h
  push Not at h
  have hcont : ∀ ψ, OrderContinuous S ψ := by
    intro ψ
    rw [OrderContinuous]
    intro A hA
    by_contra h'
    push Not at h'
    have : IsSingular S ψ := ⟨A, hA, h'⟩
    exact h ψ this
  have hsigma_cont : @Continuous S.potential S.poset
      (UniformSpace.toTopologicalSpace) S.poset_topology S.sigma :=
    sigma_continuous_of_orderContinuous S hcont
  have hconn : IsConnected (Set.univ : Set S.poset) := by
    have hpath : @IsPathConnected S.potential
        (UniformSpace.toTopologicalSpace) Set.univ :=
      isPathConnected_univ_potential S
    have hconn' : @IsConnected S.potential
        (UniformSpace.toTopologicalSpace) Set.univ :=
      IsPathConnected.isConnected hpath
    have himage : S.sigma '' Set.univ = Set.univ := by
      ext x
      simp [surj x]
    have hconn_img : IsConnected (S.sigma '' Set.univ) :=
      isConnected_image_of_continuous hconn' hsigma_cont
    rwa [himage] at hconn_img
  exact disconnected hconn

theorem singularity_set_location (S : SelectionOperator) :
    {ψ : S.potential | IsSingular S ψ} =
      ⋃ A : S.poset, frontier (S.sigma ⁻¹' {B : S.poset | A ≤ B})
        ∩ S.sigma ⁻¹' {B : S.poset | A ≤ B} := by
  ext ψ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_setOf_eq, frontier_def, closure_eq_self]
  constructor
  · intro h
    rcases h with ⟨A, hA, hA'⟩
    use A
    constructor
    · rw [@mem_frontier_iff S.potential
        (UniformSpace.toTopologicalSpace)]
      constructor
      · exact hA
      · intro hopen
        have hcont : OrderContinuous S ψ := by
          intro B hB
          have hsub : S.sigma ⁻¹' {C | B ≤ C} ⊆ S.sigma ⁻¹' {C | B ≤ C} :=
            subset_refl _
          rw [isOpen_iff_nhds] at hopen
          have hn := hopen ψ hA
          rw [Metric.mem_nhds_iff] at hn
          obtain ⟨ε, hε, hε'⟩ := hn
          exact ⟨ε, hε, hε'⟩
        obtain ⟨ε, hε, hε'⟩ := hcont A hA
        obtain ⟨ψ', hψ'1, hψ'2⟩ := hA' ε hε
        exact hψ'2 (hε' ψ' hψ'1)
    · exact hA
  · rintro ⟨A, hfront, hA⟩
    refine ⟨A, hA, ?_⟩
    intro ε hε
    rw [@mem_frontier_iff S.potential (UniformSpace.toTopologicalSpace)] at hfront
    have hn : ψ ∈ closure (S.sigma ⁻¹' {B | A ≤ B}) \ interior (S.sigma ⁻¹' {B | A ≤ B}) := hfront
    rcases hn with ⟨hcls, hint⟩
    rw [mem_interior_iff_mem_nhds] at hint
    have hn' : S.sigma ⁻¹' {B | A ≤ B} ∉ nhds ψ := by
      simpa using hint
    rw [Metric.mem_nhds_iff] at hn'
    push Not at hn'
    obtain ⟨ψ', hψ'1, hψ'2⟩ := hn' ε hε
    exact ⟨ψ', hψ'1, hψ'2⟩

def Shares (S : SelectionOperator) (ψ φ : S.potential) : Prop :=
  @inner ℝ _ _ ψ φ ≠ 0

theorem sharing_refl (S : SelectionOperator) (ψ : S.potential)
    (hψ : ψ ≠ 0) : Shares S ψ ψ := by
  rw [Shares, real_inner_self_eq_norm_sq]
  have h : ‖ψ‖ ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    rw [norm_ne_zero_iff]
    exact hψ
  exact h

theorem sharing_symm (S : SelectionOperator) (ψ φ : S.potential)
    (h : Shares S ψ φ) : Shares S φ ψ := by
  rw [Shares, real_inner_comm]
  exact h

def BandRel (S : SelectionOperator) (A B : S.poset) : Prop :=
  ∃ ψ φ : S.potential, S.sigma ψ = A ∧ S.sigma φ = B ∧ Shares S ψ φ

theorem band_trans (S : SelectionOperator) {A B C : S.poset}
    (hAB : BandRel S A B) (hBC : BandRel S B C) : BandRel S A C := by
  obtain ⟨ψ1, φ1, hσ1, hτ1, hsh1⟩ := hAB
  obtain ⟨ψ2, φ2, hσ2, hτ2, hsh2⟩ := hBC
  rw [hτ1] at hσ2
  exact ⟨ψ1, φ2, hσ1, hτ2, hsh1⟩

def Band (S : SelectionOperator) (A B : S.poset) : Prop :=
  Relation.TransGen (BandRel S) A B

theorem band_symm (S : SelectionOperator) (A B : S.poset)
    (h : Band S A B) : Band S B A := by
  induction h using Relation.TransGen.head_induction_on with
  | single hstep => exact Relation.TransGen.single (sharing_symm S _ _ hstep)
  | tail h1 h2 ih => exact Relation.TransGen.trans ih (Relation.TransGen.single h2)

end VidLeanSection5
