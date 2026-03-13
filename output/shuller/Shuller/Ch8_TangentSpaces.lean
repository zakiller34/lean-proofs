import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic

/-!
# Chapter 8: Tangent Spaces

Schuller defines tangent vectors as derivations on C^∞(M). In Mathlib,
the tangent space `TangentSpace I x` at a point x of a manifold M is
modeled as the model vector space (not via derivations). The key tool
is `mfderiv`: the derivative of a smooth map between manifolds.
-/

/-! ## Tangent Space as a Module

`TangentSpace I x` is a copy of the model space, with module structure. -/

/-- The tangent space of ℝ at any point is ℝ (as a module). -/
noncomputable example : Module ℝ (TangentSpace (modelWithCornersSelf ℝ ℝ) (0 : ℝ)) :=
  inferInstance

/-- The tangent space of ℝⁿ at a point is ℝⁿ. -/
noncomputable example (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Module ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
  inferInstance

/-! ## The Manifold Derivative (mfderiv)

`mfderiv I I' f x` is the derivative of f : M → N at x, expressed as a
continuous linear map between tangent spaces. This is Schuller's "push-forward"
of tangent vectors. -/

/-- Derivative of the identity map is the identity. Schuller Prop 8.1. -/
theorem mfderiv_of_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ⊤ M] (x : M) :
    mfderiv I I (id : M → M) x = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  mfderiv_id (I := I)

/-- The chain rule: derivative of composition is composition of derivatives.
    Schuller Prop 8.2. -/
theorem mfderiv_chain_rule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {H'' : Type*} [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'}
    {I'' : ModelWithCorners ℝ E'' H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ⊤ M']
    {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' ⊤ M'']
    {f : M → M'} {g : M' → M''} {x : M}
    (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x =
      (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) :=
  mfderiv_comp x hg hf

/-- Derivative of a constant map is zero. -/
theorem mfderiv_of_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ⊤ M']
    {c : M'} {x : M} :
    mfderiv I I' (fun _ : M => c) x = 0 :=
  mfderiv_const (I := I) (I' := I')

/-- The identity is smooth. -/
theorem smooth_id_manifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] :
    ContMDiff I I ⊤ (id : M → M) :=
  contMDiff_id

/-- A constant map is smooth. -/
theorem smooth_const_manifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ⊤ M']
    (c : M') :
    ContMDiff I I' ⊤ (fun _ : M => c) :=
  contMDiff_const

/-- The derivative mfderiv produces a continuous linear map between tangent spaces. -/
theorem mfderiv_is_clinear_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ⊤ M']
    (f : M → M') (x : M) :
    ∃ L : TangentSpace I x →L[ℝ] TangentSpace I' (f x), L = mfderiv I I' f x :=
  ⟨mfderiv I I' f x, rfl⟩
