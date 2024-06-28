import Mathlib
/-!
# Algebraic function fields of one variable

We build on what is already there in `Mathlib.NumberTheory.FunctionField`
to implement the theory of algebraic function fields of one variable over arbitrary
base fields.

TODOs relating to `Mathlib.NumberTheory.FunctionField`:
* Remove mention of finite fields in the documentation as finiteness is nowhere required or used.
* Move file to somewhere not under `NumberTheory`.
* `FunctionField` should probably be `IsFunctionField`.
* Make material universe polymorphic (currently everything is in `Type`).

For now, we set up our own version as a structure `AlgFunctionField1`.

We follow Chapter I of the textbook *Algebraic Function Fields and Codes*
by Henning Stichtenoth (Springer Universitext, 1993).
-/

/-!
### Definition of algebraic function fields of one variable
-/

section Def

open scoped IntermediateField

universe u

/-
What is in Mathlib:

variable (F FF : Type) [Field F] [Field FF]

abbrev FunctionField [Algebra (RatFunc F) FF] : Prop :=
  FiniteDimensional (RatFunc F) FF

This has the disadvantage of fixing `RatFunc F` as a "base field", but we would like
to treat `F` as the base field and have a subfield isomorphic to `RatFunc F`.

(Also, this is not universe polynomorphic and should be called `IsFunctionField`...)
-/

/-
One possible definition: this bundles a carrier type with the data of an element `x`
transcendental over the base field `F` and such that we have a finite extension of `F(x)`.
-/

variable (F : Type u) [Field F]

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

def IsFunctionField (FF : Type*) [Field FF] [Algebra F FF] : Prop :=
  ∃ (_ : Algebra (RatFunc F) FF) (_ : IsScalarTower F (RatFunc F) FF),
    FiniteDimensional (RatFunc F) FF

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

lemma RatFunc.isFunctionField : IsFunctionField F (RatFunc F) :=
  ⟨inferInstance, IsScalarTower.right, Module.Finite.self (RatFunc F)⟩

variable (f : Polynomial (RatFunc F))

variable {F} in
abbrev functionField_of_polynomial := AdjoinRoot f

noncomputable
instance [Fact <| Irreducible f] : Field (functionField_of_polynomial f) :=
  inferInstance

variable {F f} in
lemma AdjoinRoot.finiteDimensional (hf₀ : f ≠ 0) :
    FiniteDimensional (RatFunc F) (AdjoinRoot f) := by
  sorry

lemma functionField_of_polynomial.isFunctionField [hf : Fact <| Irreducible f] :
    IsFunctionField F (functionField_of_polynomial f) :=
  ⟨inferInstance, inferInstance, AdjoinRoot.finiteDimensional (Irreducible.ne_zero <| hf.out)⟩

end Def


/-!
### Places
-/

section Place

variable (F FF : Type*) [Field F] [Field FF] [Algebra F FF]

namespace IsFunctionField

/-- The *field of constants*  of an algebraic function field `FF` of one variable over `F`
is the relative algebraic closure of `F` in `FF`. -/
abbrev fieldOfConstants : Subalgebra F FF := integralClosure F FF

instance fielfOfConstants_field : Field (fieldOfConstants F FF) := by
  sorry

/-- An algebraic function field of one variable is *geometric* if its field of constants
is the base field. -/
def IsGeometric : Prop := IsFunctionField.fieldOfConstants F FF = ⊥

/-- A *place* of an algebraic function field of one variable is a valuation subring that contains
the base field. -/
structure Place extends ValuationSubring FF, Subalgebra F FF

#check Place.toValuationSubring
#check Place.toSubalgebra

variable {F FF}

lemma Place.isLocalRing (v : IsFunctionField.Place F FF) : LocalRing v.toValuationSubring :=
  inferInstance

#check ValuationRing.instIsBezout
#check IsBezout.nonemptyGCDMonoid
#check GCDMonoid.toIsIntegrallyClosed


instance {O} [CommRing O] [IsDomain O] [ValuationRing O] : IsIntegrallyClosed O :=
  inferInstance

lemma _root_.IsIntegral.subalgebra (A : Subalgebra F FF) (x : FF) (hx : IsIntegral F x) : IsIntegral A x := by
  obtain ⟨p, hp_monic, hp⟩ := hx
  use p.map (algebraMap F A)
  rw [Polynomial.eval₂_map]
  refine ⟨hp_monic.map _, hp⟩

lemma _root_.integralClosure_le_subAlgebra_of_isIntegrallyClosedIn (A : Subalgebra F FF) [hA : IsIntegrallyClosedIn A FF] :
    integralClosure F FF ≤ A := by
  intro x hx
  have : IsIntegral A x := IsIntegral.subalgebra A x hx
  rw [IsIntegrallyClosedIn.isIntegral_iff] at this
  obtain ⟨⟨y, hy⟩, rfl⟩ := this
  exact hy

lemma Place.isFractionRing (v : IsFunctionField.Place F FF) : IsFractionRing v.toSubalgebra FF := ValuationSubring.instIsFractionRingSubtypeMem ..

lemma Place.fieldOfConstants_le (v : IsFunctionField.Place F FF) :
    IsFunctionField.fieldOfConstants F FF ≤ v.toSubalgebra :=
  have : IsFractionRing v.toSubalgebra FF := v.isFractionRing
  have : IsIntegrallyClosedIn v.toSubalgebra FF := by
    apply isIntegrallyClosed_iff_isIntegrallyClosedIn FF |>.mp
    infer_instance
  integralClosure_le_subAlgebra_of_isIntegrallyClosedIn _

  /- rw [SetLike.le_def, fieldOfConstants]
  intro z hz
  contrapose! hz
  intro h
  have hz₀ : z ≠ 0 := by
    contrapose! hz
    rw [hz]
    exact Subalgebra.zero_mem v.toSubalgebra
  have hz' : z⁻¹ ∈ v.toValuationSubring := (ValuationSubring.mem_or_inv_mem _ _).resolve_left hz
  have hz'' : z⁻¹ ∈ integralClosure F FF := sorry
    -- adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hz) int.inv_mem_adjoin h
  obtain ⟨p, hpm, hp⟩ : IsIntegral F z := h
  have hpd : 1 ≤ p.natDegree := sorry
  have hz_eq :
      z = -(p - Polynomial.X ^ p.natDegree).eval₂ (algebraMap F FF) z * (z⁻¹) ^ (p.natDegree - 1) := by
    simp only [Polynomial.eval₂_sub, hp, Polynomial.eval₂_X_pow, zero_sub, neg_neg, inv_pow]
    have help : z ^ p.natDegree = z ^ (1 + (p.natDegree - 1)) := by
      congr
      exact (Nat.add_sub_of_le hpd).symm
    rw [help, pow_add, pow_one, mul_assoc, mul_inv_cancel (pow_ne_zero (p.natDegree - 1) hz₀),
      mul_one]
  have hzi : Invertible z := invertibleOfNonzero hz₀
  rw [← Polynomial.eval₂_reverse_eq_zero_iff (algebraMap F FF) z p, invOf_eq_inv] at hp
  have hz_eq' : z = -(p.reverse / Polynomial.X).eval₂ (algebraMap F FF) z⁻¹ := by
    #check Polynomial.divX
    sorry
  contrapose! hz
  rw [hz_eq']
  simp only [neg_mem_iff, Polynomial.eval₂, Polynomial.sum]
  refine Subalgebra.sum_mem v.toSubalgebra fun i hi ↦ ?_
  refine Subalgebra.mul_mem v.toSubalgebra ?_ <| Subalgebra.pow_mem _ hz' i
  exact Subalgebra.algebraMap_mem v.toSubalgebra ((p.reverse / Polynomial.X).coeff i) -/



end IsFunctionField

end Place

#exit
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
