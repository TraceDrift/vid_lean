import VidLean.Basic
import Mathlib.Order.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace VidLean

/-- VID v2.0 §5.1: Selection operator.
The directive's skeleton carried the order as a structure instance field,
which is not valid Lean 4, and used `NormedSpace ℝ` (Analysis) for the metric
structure; the order and a `PseudoMetricSpace` (Topology; suffices for
`dist`) are therefore type-class parameters of the structure. -/
structure SelectionOperator
    (potential : Type*) [PseudoMetricSpace potential]
    (poset : Type*) [PartialOrder poset] where
  sigma : potential → poset   -- selection map (name `sigma` per directive; not the unicode `Σ`)

/-- VID v2.0 §5.3: Upset topology on a poset (fully proved). -/
def upsetTopology (L : Type*) [PartialOrder L] : TopologicalSpace L where
  IsOpen U := ∀ x ∈ U, ∀ y, x ≤ y → y ∈ U
  isOpen_univ := fun _ _ _ _ => trivial
  isOpen_inter := fun U V hU hV x hx y hxy =>
    ⟨hU x hx.1 y hxy, hV x hx.2 y hxy⟩
  isOpen_sUnion := fun S h x hx y hxy => by
    obtain ⟨U, hU, hxU⟩ := hx
    exact ⟨U, hU, h U hU x hxU y hxy⟩

/-- VID v2.0 §5.2: Order-continuity of the selection map at ψ. -/
def OrderContinuous
    {potential : Type*} [PseudoMetricSpace potential]
    {poset : Type*} [PartialOrder poset]
    (S : SelectionOperator potential poset) (ψ : potential) : Prop :=
  ∀ A : poset, A ≤ S.sigma ψ →
    ∃ ε > 0, ∀ ψ', dist ψ ψ' < ε → A ≤ S.sigma ψ'

/-- VID v2.0 §5.2: Singularity (a selected attribute is lost under arbitrarily
small perturbations of the potential). -/
def IsSingular
    {potential : Type*} [PseudoMetricSpace potential]
    {poset : Type*} [PartialOrder poset]
    (S : SelectionOperator potential poset) (ψ : potential) : Prop :=
  ∃ A : poset, A ≤ S.sigma ψ ∧
    ∀ ε > 0, ∃ ψ', dist ψ ψ' < ε ∧ ¬ A ≤ S.sigma ψ'

/-- VID v2.0 Theorem 5.5: Topological criterion (iff).
Openness of the preimage is taken in the metric topology of `potential`;
the set `{B | A ≤ B}` is the principal upset, which is open in the upset
topology on `poset`. -/
theorem orderContinuous_iff_preimages_open
    (potential : Type*) [PseudoMetricSpace potential]
    (poset : Type*) [PartialOrder poset] [TopologicalSpace poset]
    (S : SelectionOperator potential poset) :
    (∀ ψ, OrderContinuous S ψ) ↔
    (∀ A : poset, IsOpen (S.sigma ⁻¹' {B : poset | A ≤ B})) := by
  sorry  -- TO BE PROVED: forward by interior point argument, reverse by definition

/-- VID v2.0 Theorem 5.6: Existence of singularities. -/
theorem singularity_exists
    (potential : Type*) [PseudoMetricSpace potential]
    (poset : Type*) [PartialOrder poset] [TopologicalSpace poset]
    (S : SelectionOperator potential poset)
    (surj : Function.Surjective S.sigma)
    (disconnected : ¬ IsConnected (Set.univ : Set poset)) :
    ∃ ψ, IsSingular S ψ := by
  sorry  -- TO BE PROVED: by contradiction using connectedness

end VidLean
