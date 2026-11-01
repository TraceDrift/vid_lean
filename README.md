# vid_lean — VID v2.0 Ground Layer in Lean 4

Lean 4 formalization of **VID v2.0, §2 (Difference Space) and §5 (Selection Operator & Singularity)**.
Target: CPP 2027 submission. Hard proofs are admitted with `sorry` and flagged for future work.

## Installation

```bash
git clone https://github.com/TraceDrift/vid_lean.git
cd vid_lean
lake exe cache get  # Download mathlib cache (~10 min)
lake build          # Build project (~10 min)
```

Toolchain: `leanprover/lean4:v4.9.0` (see `lean-toolchain`; use [elan](https://github.com/leanprover/elan)).
Expected: **build completes with 0 errors**; exactly 4 `sorry` warnings (the admitted theorems below).

## Usage

Open `VidLean/Basic.lean` in VS Code with the Lean 4 extension.

## Contents

| File | Content | Status |
|---|---|---|
| `VidLean/Basic.lean` | `DifferenceSpace` (Definition 2.1), Axioms 2.3/2.5/2.6, witness `M'` (Definition 2.2), Theorem 2.9 `cardinality_bound` (\|D\| ≥ 3) | fully proved except `cardinality_bound` (`sorry`) |
| `VidLean/Selection.lean` | `SelectionOperator` (Definition 5.1), `upsetTopology` (Definition 5.2, **fully proved**), `OrderContinuous` (5.3), `IsSingular`, Theorem 5.5 `orderContinuous_iff_preimages_open` (`sorry`), Theorem 5.6 `singularity_exists` (`sorry`) | topology part proved |
| `VidLean/Singularity.lean` | Corollary 5.9 `singularity_set_location` (`sorry`) | admitted |
| `VidLean.lean` | root imports | — |

## TODO (CPP 2027)

- Prove `cardinality_bound` from the axioms (or derive a contradiction — see deviation note on `self_diff_ne_self`).
- Prove Theorems 5.5, 5.6 and Corollary 5.9.
- Extend to §6+ (shuttle group).

## Formalization notes — deviations from the build directive

All flagged, none silent:

1. `Σ` → `sigma`: `Σ` is a reserved notation token in Lean 4.9 and cannot start an identifier; the projection operator field is named `sigma` throughout.
2. `[NormedAddCommGroup potential]` → `[PseudoMetricSpace potential]` + `import Mathlib.Topology.MetricSpace.Basic`: `NormedAddCommGroup` lives in Mathlib's Analysis layer, not reachable from the directive's import list; the pseudo-metric-space formulation covers everything the formalization uses (`dist`, `Metric`).
3. `import Mathlib.Topology.Connected` → `Mathlib.Topology.Connected.Basic`: at v4.9.0 `Connected` is a directory.
4. `Connected (univ)` → `¬ IsConnected (Set.univ : Set poset)`: the v4.9.0 predicate is `IsConnected : Set α → Prop` (Theorem 5.6 hypothesis).
5. Non-associativity witness for `M'` changed from the draft triple (0,1,2) — which actually *is* associative for the given `opTable` — to (0,0,1), where `opTable (opTable 0 0) 1 = 2 ≠ 1 = opTable 0 (opTable 0 1)`. Comment in `Basic.lean` shows the check.
6. `Nat.card` → `Fintype.card` with a `[Fintype S.D]` parameter: `Nat.card` is not available at v4.9.0 with the imported modules.

(Build-environment-only patches from the offline sandbox — proofwidgets `preferReleaseBuild := false` and batteries doc-gen4 removal — do not apply to this standard git-dependency checkout.)

## License / attribution

Formalizes Trace Drift, *Virtual Invasion Dynamics* v2.0, §2 and §5.
