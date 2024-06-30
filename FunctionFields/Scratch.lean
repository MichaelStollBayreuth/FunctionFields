import FunctionFields.Basic

#exit

/-
### Alternative attempts
-/


/-
One possible definition: this bundles a carrier type with the data of an element `x`
transcendental over the base field `F` and such that we have a finite extension of `F(x)`.
-/

structure AlgFunctionField1 : Type (u + 1) where
  /-- The carrier type -/
  carrier : Type u
  /-- The carrier type must be a field. -/
  field : Field carrier
  /-- The carrier type must be an algebra over the base field. -/
  algebra : Algebra F carrier
  /-- An element of the function field that is transcendental over `F` -/
  x : carrier
  /-- `x` is transcendental over `F`. -/
  nonalg : ¬ IsAlgebraic F x
  /-- The function field is finite-dimensional over the rational function field `F(x)`. -/
  finite_dim : FiniteDimensional F⟮x⟯ carrier

attribute [instance] AlgFunctionField1.field AlgFunctionField1.algebra

lemma RatFunc.aeval_X_eq_algebraMap (p : Polynomial F) :
    Polynomial.aeval X p = algebraMap _ (RatFunc F) p := by
  rw [← algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

/-- The rational function field in one variable as an algebraic function field in one variable. -/
noncomputable
def RatFunc.toAlgFunctionField1 : AlgFunctionField1 F where
  carrier := RatFunc F
  field := inferInstance
  algebra := inferInstance
  x := X
  nonalg := by
    rw [isAlgebraic_iff_not_injective, not_not, injective_iff_map_eq_zero]
    intro p
    simp only [aeval_X_eq_algebraMap, algebraMap_eq_zero_iff, imp_self]
  finite_dim := by
    have : F⟮X⟯ = (⊤ : IntermediateField F (RatFunc F)) := by
      refine IntermediateField.ext fun a ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
      rw [IntermediateField.mem_adjoin_simple_iff]
      exact ⟨a.num, a.denom, by simp only [aeval_X_eq_algebraMap, num_div_denom]⟩
    exact this ▸ Module.finite_of_rank_eq_one IntermediateField.rank_top

/-
An alternative is to define a characteristic predicate:
-/

def IsFunctionField' (FF : Type*) [Field FF] [Algebra F FF] : Prop :=
  ∃ x : FF, ¬ IsAlgebraic F x ∧ FiniteDimensional F⟮x⟯ FF


lemma isFunctionField'_iff_isFunctionField (FF : Type*) [Field FF] [Algebra F FF] :
    IsFunctionField' F FF ↔ IsFunctionField F FF := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · obtain ⟨x, hx, h⟩ := H
    have nzd : nonZeroDivisors (Polynomial F) ≤ Submonoid.comap (Polynomial.eval₂RingHom (algebraMap F FF) x) (nonZeroDivisors FF) := sorry
    let φ : RatFunc F →+* FF := RatFunc.liftRingHom (Polynomial.eval₂RingHom (algebraMap F FF) x) nzd
    let alg := φ.toAlgebra
    refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a ↦ ?_, ?_⟩
    · rw [show algebraMap (RatFunc F) FF = φ from rfl, RatFunc.algebraMap_eq_C,
        RatFunc.liftRingHom_apply]
      simp only [RatFunc.num_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RatFunc.denom_C,
        map_one, div_one]
    · have hφ : φ.range = F⟮x⟯.toSubring := sorry
      have : Module (RatFunc F) ↥F⟮x⟯.toSubring := by
        convert_to Module (RatFunc F) ↥φ.range
        · rw [hφ]
        · sorry
        sorry -- apply Algebra.toModule
      have : IsScalarTower (RatFunc F) (↥F⟮x⟯.toSubring) FF := sorry
      have H₁ : Module.Finite (RatFunc F) ↥F⟮x⟯.toSubring := sorry
      have H₂ : Module.Finite (↥F⟮x⟯.toSubring) FF := sorry
      exact Module.Finite.trans F⟮x⟯.toSubring FF
  · sorry

lemma RatFunc.isFunctionField' : IsFunctionField' F (RatFunc F) := by
  refine ⟨X, ?_, ?_⟩
  · rw [isAlgebraic_iff_not_injective, not_not, injective_iff_map_eq_zero]
    intro p
    simp only [aeval_X_eq_algebraMap, algebraMap_eq_zero_iff, imp_self]
  · have : F⟮X⟯ = (⊤ : IntermediateField F (RatFunc F)) := by
      refine IntermediateField.ext fun a ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
      rw [IntermediateField.mem_adjoin_simple_iff]
      exact ⟨a.num, a.denom, by simp only [aeval_X_eq_algebraMap, num_div_denom]⟩
    exact this ▸ Module.finite_of_rank_eq_one IntermediateField.rank_top

namespace AlgFunctionField1

variable {F : Type*} [Field F] (FF : AlgFunctionField1 F)

/-- The *field of constants*  of an algebraic function field `FF` of one variable over `F`
is the relative algebraic closure of `F` in `FF`. -/
def fieldOfConstants : Subalgebra F FF.carrier := integralClosure F FF.carrier

/-- An algebraic function field of one variable is *geometric* if its field of constants
is the base field. -/
def IsGeometric : Prop := FF.fieldOfConstants = ⊥

/-- A *place* of an algebraic function field of one variable is a valuation subring that contains
the base field. -/
structure Place extends ValuationSubring (FF.carrier) where
  trivial_on_base_field :
      (IntermediateField.toSubalgebra (⊥ : IntermediateField F FF.carrier)).toSubring ≤ carrier

variable {FF}

/-- The valuation ring corresponding to a place as a subalgebra. -/
def Place.toSubalgebra (v : Place FF) : Subalgebra F FF.carrier where
  carrier := v.carrier
  mul_mem' := v.mul_mem'
  add_mem' := v.add_mem'
  algebraMap_mem' r :=
    sorry

lemma Place.fieldOfConstants_le (v : Place FF) : FF.fieldOfConstants ≤ v.toSubalgebra := by
  sorry

end AlgFunctionField1
