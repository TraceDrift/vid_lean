import VidLean.Selection

namespace VidLean

/-- VID v2.0 Corollary 5.9: Singularity set location.
A potential is singular iff it lies on the boundary of the preimage of some
principal upset, i.e. on the frontier of a selection fiber. -/
theorem singularity_set_location
    (potential : Type*) [PseudoMetricSpace potential]
    (poset : Type*) [PartialOrder poset] [TopologicalSpace poset]
    (S : SelectionOperator potential poset) :
    {ψ | IsSingular S ψ} =
    ⋃ A : poset, (closure (S.sigma ⁻¹' {B : poset | A ≤ B})) \
                 interior (S.sigma ⁻¹' {B : poset | A ≤ B}) := by
  sorry  -- TO BE PROVED: fiber boundary characterization

end VidLean
