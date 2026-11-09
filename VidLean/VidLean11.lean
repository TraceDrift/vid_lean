import Mathlib
import VidLean9

-- VIDLEAN BUILD VidLean11-v3-20261109

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.tacticAnalysis.introMerge false

noncomputable section

namespace VidLean11

open VidLean8 VidLean9

def HasOpenFibers (S : SelectionOperator) : Prop :=
  ∀ A : S.poset, IsOpen (S.sigma ⁻¹' {A})

theorem no_singular_of_open_fibers (S : SelectionOperator)
    (h : HasOpenFibers S) : ∀ ψ, ¬ VidLean8.IsSingular S ψ := by
  intro ψ
  have hloc : VidLean10.IsLocallyConstantAt S ψ := by
    use 1
    constructor
    · norm_num
    · intro ψ' hdist
      have h1 : S.sigma ψ' ∈ ({S.sigma ψ'} : Set S.poset) := Set.mem_singleton _
      have h2 : S.sigma ψ ∈ ({S.sigma ψ} : Set S.poset) := Set.mem_singleton _
      have hopen := h (S.sigma ψ)
      have hopen' := h (S.sigma ψ')
      have hne : dist ψ ψ' < 1 := hdist
      have h3 : ψ' ∈ S.sigma ⁻¹' {S.sigma ψ'} := by simp
      have h4 : ψ ∈ S.sigma ⁻¹' {S.sigma ψ} := by simp
      have h5 : S.sigma ψ' = S.sigma ψ := by
        by_contra hne'
        have hsep : SeparatedNhds (S.sigma ⁻¹' {S.sigma ψ}) (S.sigma ⁻¹' {S.sigma ψ'}) := by
          apply T2Space.t2
          simp [hne']
        obtain ⟨U, V, hU, hV, hUV, hsubU, hsubV⟩ := hsep
        have h6 : ψ ∈ U := hsubU h4
        have h7 : ψ' ∈ V := hsubV h3
        rw [isOpen_iff_nhds] at hU hV
        have hnU := hU ψ h6
        have hnV := hV ψ' h7
        rw [Metric.mem_nhds_iff] at hnU hnV
        obtain ⟨ε1, hε1, hε1'⟩ := hnU
        obtain ⟨ε2, hε2, hε2'⟩ := hnV
        let δ := min ε1 ε2
        have hδ : δ > 0 := lt_min hε1 hε2
        have h8 : dist ψ ψ' < δ := by linarith [hdist, hδ]
        have h9 : ψ' ∈ U := hε1' ψ' (by linarith [min_le_left ε1 ε2, h8])
        have h10 : ψ' ∈ V := hε2' ψ' (by linarith [min_le_right ε1 ε2, h8])
        have h11 : U ∩ V = ∅ := hUV
        have h12 : ψ' ∈ U ∩ V := ⟨h9, h10⟩
        rw [h11] at h12
        exact h12
      exact h5
    exact hloc
  exact VidLean10.no_singular_of_locally_constant S ψ hloc

end VidLean11
