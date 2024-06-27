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

def IsFunctionField (FF : Type*) [Field FF] [Algebra F FF] : Prop :=
  ∃ x : FF, ¬ IsAlgebraic F x ∧ FiniteDimensional F⟮x⟯ FF

lemma RatFunc.isFunctionField : IsFunctionField F (RatFunc F) := by
  refine ⟨X, ?_, ?_⟩
  · rw [isAlgebraic_iff_not_injective, not_not, injective_iff_map_eq_zero]
    intro p
    simp only [aeval_X_eq_algebraMap, algebraMap_eq_zero_iff, imp_self]
  · have : F⟮X⟯ = (⊤ : IntermediateField F (RatFunc F)) := by
      refine IntermediateField.ext fun a ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
      rw [IntermediateField.mem_adjoin_simple_iff]
      exact ⟨a.num, a.denom, by simp only [aeval_X_eq_algebraMap, num_div_denom]⟩
    exact this ▸ Module.finite_of_rank_eq_one IntermediateField.rank_top

end Def

namespace AlgFunctionField1

variable {F : Type*} [Field F] (FF : AlgFunctionField1 F)

/-- The *field of constants*  of an algebraic function field `FF` of one variable over `F`
is the relative algebraic closure of `F` in `FF`. -/
def fieldOfConstants : Subalgebra F FF.carrier := integralClosure F FF.carrier

/-- An algebraic function field of one variable is *geometric* if its field of constants
is the base field. -/
def IsGeometric : Prop := FF.fieldOfConstants = ⊥

/-!
### Places
-/

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

section IsFF

variable {F FF : Type*} [Field F] [Field FF] [Algebra F FF] (hF : IsFunctionField F FF)

namespace IsFunctionField

variable (F FF) in
/-- The *field of constants*  of an algebraic function field `FF` of one variable over `F`
is the relative algebraic closure of `F` in `FF`. -/
def fieldOfConstants : Subalgebra F FF := integralClosure F FF

/-- An algebraic function field of one variable is *geometric* if its field of constants
is the base field. -/
def IsGeometric : Prop := IsFunctionField.fieldOfConstants F FF = ⊥

/-- A *place* of an algebraic function field of one variable is a valuation subring that contains
the base field. -/
structure Place extends ValuationSubring FF, Subalgebra F FF

#check Place.toValuationSubring
#check Place.toSubalgebra

end IsFunctionField

end IsFF
