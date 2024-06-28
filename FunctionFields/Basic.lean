import Mathlib.NumberTheory.FunctionField
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
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

-- `F` is the base field of our function fields.
variable (F : Type u) [Field F]

/-
In the discussion during work on this project on Thursday at the AIM workshop,
we decided to use the definition Junyan proposed (which is `IsFunctionField` below).
-/

/-- An `F`-algebra `FF` is an (algebraic) *function field* (of one variable) if there is a
scalar tower `F → RatFunc F → FF` and `FF` is finite-dimensional over `RatFunc F`. -/
def IsFunctionField (FF : Type*) [Field FF] [Algebra F FF] : Prop :=
  ∃ (_ : Algebra (RatFunc F) FF) (_ : IsScalarTower F (RatFunc F) FF),
    FiniteDimensional (RatFunc F) FF

/-- The rational function field `RatFunc F` is a function field over `F`. -/
lemma RatFunc.isFunctionField : IsFunctionField F (RatFunc F) :=
  ⟨inferInstance, IsScalarTower.right, Module.Finite.self (RatFunc F)⟩

/-- The field obtained by adjoining the root of an irreducible polynomial `f ∈ F(X)[Y]`
to the rational function field over `F` is a function field. -/
lemma Polynomial.adjoinRoot_isFunctionField (f : Polynomial (RatFunc F))
    [hf : Fact <| Irreducible f] :
    IsFunctionField F (AdjoinRoot f) :=
  ⟨inferInstance, inferInstance,
    PowerBasis.finite <| AdjoinRoot.powerBasis (Irreducible.ne_zero <| hf.out)⟩

/-
We can relate our definition to the definition currently in Mathlib.
(This is slightly awkward as we need to produce suitable instances on the fly.)
-/

lemma FunctionField.isFunctionField {F FF : Type} [Field F] [Field FF] [Algebra (RatFunc F) FF]
    (h : FunctionField F FF) :
    letI inst := (algebraMap (RatFunc F) FF).comp (algebraMap F (RatFunc F)) |>.toAlgebra
    IsFunctionField F FF := by
  let inst := ((algebraMap (RatFunc F) FF).comp (algebraMap F (RatFunc F))).toAlgebra
  refine ⟨inferInstance, IsScalarTower.of_algebraMap_eq (congrFun rfl), h⟩

lemma IsFunctionField.functionField {F FF : Type} [Field F] [Field FF] [Algebra F FF]
    (h : IsFunctionField F FF) :
    letI inst := Classical.choose h
    FunctionField F FF :=
  Classical.choose_spec <| Classical.choose_spec h

end Def

section Transcendental
/-!
### Transcendental elements

The goal here is to show that if `x : FF` is transcendental over `F`, then
`F⟮x⟯` is isomorphic as an `F`-algebra to `RatFunc F`.
-/

open scoped IntermediateField

variable {F FF} [Field F] [Field FF] [Algebra F FF]

def RatFunc.algHom_of_not_isAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x) :
    RatFunc F →ₐ[F] FF := by
  refine liftAlgHom (Polynomial.aeval x) fun c hc ↦ ?_
  simp only [mem_nonZeroDivisors_iff, mul_eq_zero, forall_eq_or_imp, true_and, Submonoid.mem_comap,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  intro _ h
  exfalso
  apply hx
  rw [isAlgebraic_iff_not_injective, injective_iff_map_eq_zero]
  push_neg
  exact ⟨_, h, nonZeroDivisors.ne_zero hc⟩

/- noncomputable
def RatFunc.algEquiv_of_not_isAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x) :
    RatFunc F ≃ₐ[F] F⟮x⟯ := by
  let f := algHom_of_not_isAlgebraic hx
  refine AlgEquiv.ofBijective f ?_ -/


end Transcendental


section Place

/-!
### Places
-/

/-
NOTE: Junyan has the definition of `Place` (in greater generality) and `Place.integralClosure_le`
in #14206
-/

variable (F FF : Type*) [Field F] [Field FF] [Algebra F FF]

namespace IsFunctionField

/-- The *field of constants*  of an `F`-agebra `FF` that is a field is the relative algebraic
closure of `F` in `FF`. -/
abbrev fieldOfConstants : Subalgebra F FF := integralClosure F FF

/-- An algebraic function field of one variable is *geometric* if its field of constants
is the base field. -/
def IsGeometric : Prop := fieldOfConstants F FF = ⊥

/-- A *place* of a field that is an `F`-algebra is a valuation subring that contains
the base field. -/
structure Place extends ValuationSubring FF, Subalgebra F FF

variable {F FF}

lemma Place.isLocalRing (v : Place F FF) : LocalRing v.toValuationSubring :=
  inferInstance

-- A shortcut instance for speeding up tc synthesis below
instance {O} [CommRing O] [IsDomain O] [ValuationRing O] : IsIntegrallyClosed O :=
  inferInstance

-- compare #14206. Can be removed once #14206 is merged.
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

lemma Place.isFractionRing (v : Place F FF) : IsFractionRing v.toSubalgebra FF :=
  ValuationSubring.instIsFractionRingSubtypeMem ..

/-- The valuation ring corresponding to a place contains the field of constants. -/
lemma Place.fieldOfConstants_le (v : Place F FF) : fieldOfConstants F FF ≤ v.toSubalgebra :=
  have : IsFractionRing v.toSubalgebra FF := v.isFractionRing
  have : IsIntegrallyClosedIn v.toSubalgebra FF :=
    isIntegrallyClosed_iff_isIntegrallyClosedIn FF |>.mp inferInstance
  integralClosure_le_subAlgebra_of_isIntegrallyClosedIn _

end IsFunctionField

end Place
#minimize_imports
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
