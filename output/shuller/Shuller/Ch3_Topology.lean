import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Chapter 3: Topological Spaces

Schuller defines topology as the structure enabling continuity and
convergence. Key concepts: open/closed sets, Hausdorff (T2),
compactness, paracompactness, and the Heine-Borel theorem.
-/

/-! ## Topology Axioms

Schuller defines a topology 𝒪 ⊆ 𝒫(M) satisfying:
1. ∅ ∈ 𝒪 and M ∈ 𝒪
2. Closed under finite intersections
3. Closed under arbitrary unions

In Mathlib, `TopologicalSpace` encodes this. We restate the axioms
as theorems about any topological space. -/

variable {X : Type*} [TopologicalSpace X]

/-- The empty set is open. -/
theorem empty_is_open : IsOpen (∅ : Set X) :=
  isOpen_empty

/-- The whole space is open. -/
theorem univ_is_open : IsOpen (Set.univ : Set X) :=
  isOpen_univ

/-- Finite intersection of open sets is open. -/
theorem inter_open (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ∩ V) :=
  hU.inter hV

/-- Arbitrary union of open sets is open. -/
theorem sUnion_open (S : Set (Set X)) (hS : ∀ U ∈ S, IsOpen U) :
    IsOpen (⋃₀ S) :=
  isOpen_sUnion hS

/-- A set is closed iff its complement is open. -/
theorem closed_iff_complement_open (S : Set X) :
    IsClosed S ↔ IsOpen Sᶜ :=
  isOpen_compl_iff.symm

/-! ## Hausdorff (T2) Spaces

Schuller: Distinct points have disjoint neighborhoods.
Essential for uniqueness of limits. -/

/-- In a T2 space, distinct points are separated by open sets. -/
theorem t2_separation' [T2Space X] (x y : X) (hne : x ≠ y) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  obtain ⟨U, V, hU, hV, hxU, hyV, hd⟩ := T2Space.t2 hne
  exact ⟨U, V, hU, hV, hxU, hyV, hd⟩

/-- ℝ is a Hausdorff space. -/
theorem real_is_t2 : T2Space ℝ :=
  inferInstance

/-! ## Compactness

Schuller: Every open cover has a finite subcover. -/

/-- A compact set has a finite subcover for any open cover. -/
theorem compact_has_finite_subcover {K : Set X} (hK : IsCompact K)
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι), K ⊆ ⋃ i ∈ s, U i := by
  exact hK.elim_finite_subcover U hU hcover

/-- The closed interval [0,1] is compact in ℝ. -/
theorem unit_interval_compact : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc

/-! ## Heine-Borel Theorem

Schuller: In ℝ^d, compact ↔ closed and bounded. -/

/-- In ℝ, a set is compact iff it is closed and bounded. -/
theorem heine_borel_real (S : Set ℝ) :
    IsCompact S ↔ IsClosed S ∧ Bornology.IsBounded S := by
  constructor
  · intro hK
    exact ⟨hK.isClosed, hK.isBounded⟩
  · intro ⟨hcl, hbd⟩
    exact Metric.isCompact_of_isClosed_isBounded hcl hbd

/-! ## Paracompactness

Schuller: Every open cover has a locally finite open refinement.
Crucial for partitions of unity. -/

/-- A compact space is paracompact. -/
theorem compact_implies_paracompact [CompactSpace X] :
    ParacompactSpace X :=
  inferInstance

/-- ℝ is paracompact (as a locally compact, σ-compact, Hausdorff space). -/
theorem real_is_paracompact : ParacompactSpace ℝ :=
  inferInstance

/-! ## Discrete and Indiscrete Topologies -/

/-- In the discrete topology, every set is open. -/
theorem discrete_every_set_open {α : Type*} [TopologicalSpace α]
    [DiscreteTopology α] (S : Set α) : IsOpen S :=
  isOpen_discrete S

/-- In the discrete topology, every set is closed. -/
theorem discrete_every_set_closed {α : Type*} [TopologicalSpace α]
    [DiscreteTopology α] (S : Set α) : IsClosed S := by
  rw [← isOpen_compl_iff]
  exact isOpen_discrete _
