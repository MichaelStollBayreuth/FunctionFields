import Mathlib.NumberTheory.FunctionField
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib

set_option lang.lemmaCmd true -- why should this be necessary here?

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

Authors: Arend Mellendijk, Michael Stoll, Junyan Xu
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

-- #check IntermediateField.adjoin_simple_adjoin_simple
-- #check IntermediateField.AdjoinSimple.gen
-- #check IntermediateField.AdjoinSimple.coe_gen

lemma IntermediateField.adjoin_le_iff' {S : Set FF} {E : IntermediateField F FF} :
    IntermediateField.adjoin F S ≤ E ↔ S ⊆ E :=
  IntermediateField.adjoin_le_iff

def RatFunc.algHom_intermediateField_of_not_isAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x) :
    RatFunc F →ₐ[F] F⟮x⟯ :=
  letI x' := IntermediateField.AdjoinSimple.gen F x
  liftAlgHom (Polynomial.aeval x') fun c hc ↦ by
    simp only [mem_nonZeroDivisors_iff, mul_eq_zero, forall_eq_or_imp, true_and, Submonoid.mem_comap,
      Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    intro _ h
    exfalso
    apply hx
    rw [isAlgebraic_iff_not_injective, injective_iff_map_eq_zero]
    push_neg
    refine ⟨_, ?_, nonZeroDivisors.ne_zero hc⟩
    have := IntermediateField.AdjoinSimple.coe_gen F x
    have : Polynomial.aeval x c = Polynomial.aeval x' c := by
      simp_rw [←this]
      exact Subalgebra.aeval_coe F⟮x⟯.toSubalgebra (IntermediateField.AdjoinSimple.gen F x) c
    simp [this, h]

lemma RatFunc.algHom_intermediateField_of_not_isAlgebraic_bijective {x : FF} (hx : ¬ IsAlgebraic F x) :
    Function.Bijective (algHom_intermediateField_of_not_isAlgebraic hx) := by
  refine ⟨?_, ?_⟩
  · exact (injective_iff_map_eq_zero (algHom_intermediateField_of_not_isAlgebraic hx)).2
      fun a ↦ (map_eq_zero _).mp
  · refine AlgHom.fieldRange_eq_top.mp ?_

    sorry

/-- The `F`-algebra homomorphism from `RatFunc F` to `FF` given by evaluating at a
transcendental element of `FF`. -/
def RatFunc.algHom_of_not_isAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x) :
    RatFunc F →ₐ[F] FF :=
 (IntermediateField.val F⟮x⟯).comp (RatFunc.algHom_intermediateField_of_not_isAlgebraic hx)

def RatFunc.algebraOfNotIsAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x) :
    Algebra (RatFunc F) F⟮x⟯ := (RatFunc.algHom_intermediateField_of_not_isAlgebraic hx).toAlgebra


lemma tmp {x : FF} (hx : ¬ IsAlgebraic F x) : let _ : Module (RatFunc F) F⟮x⟯ := RatFunc.algebraOfNotIsAlgebraic hx |>.toModule; FiniteDimensional (RatFunc F) F⟮x⟯ := sorry

lemma isFunctionField_of_not_isAlgebraic {x : FF} (hx : ¬ IsAlgebraic F x)
    (hfin : FiniteDimensional F⟮x⟯ FF) :
    IsFunctionField F FF := by
  let φ := RatFunc.algHom_of_not_isAlgebraic hx
  let inst : Algebra (RatFunc F) FF := φ.toRingHom.toAlgebra
  refine ⟨inst, IsScalarTower.of_algHom φ, ?_⟩
  let _ : Algebra (RatFunc F) F⟮x⟯ := RatFunc.algebraOfNotIsAlgebraic hx
  convert FiniteDimensional.trans (RatFunc F) F⟮x⟯ FF
  · exact IsScalarTower.of_algebraMap_eq' rfl
  exact tmp hx
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

lemma exists_place {x : FF} (hx : ¬ IsAlgebraic F x) : ∃ (v : Place F FF) (h : x ∈ v.toSubalgebra), ¬ IsUnit (⟨x, h⟩ : v.toSubalgebra) :=
  sorry

lemma Place.isFractionRing (v : Place F FF) : IsFractionRing v.toSubalgebra FF :=
  ValuationSubring.instIsFractionRingSubtypeMem ..

/-- The valuation ring corresponding to a place contains the field of constants. -/
lemma Place.fieldOfConstants_le (v : Place F FF) : fieldOfConstants F FF ≤ v.toSubalgebra :=
  have : IsFractionRing v.toSubalgebra FF := v.isFractionRing
  have : IsIntegrallyClosedIn v.toSubalgebra FF :=
    isIntegrallyClosed_iff_isIntegrallyClosedIn FF |>.mp sorry -- inferInstance
  integralClosure_le_subAlgebra_of_isIntegrallyClosedIn _

variable (v : Place F FF)

abbrev Place.ResidueField := LocalRing.ResidueField v.toValuationSubring

noncomputable instance : Algebra F v.ResidueField :=
  (algebraMap v.toSubalgebra v.ResidueField).comp (algebraMap F v.toSubalgebra) |>.toAlgebra

noncomputable def Place.degree (v : Place F FF) : ℕ :=
  FiniteDimensional.finrank F v.ResidueField

instance Place.instIsNoetherianRing (h : IsFunctionField F FF) (v : Place F FF) : IsNoetherianRing v.toSubalgebra := by
  sorry

instance (h : IsFunctionField F FF) (v : Place F FF) (h_field : ¬ IsField v.toSubalgebra) : DiscreteValuationRing v.toSubalgebra := by
  have : IsNoetherianRing v.toSubalgebra := by exact Place.instIsNoetherianRing h v
  sorry
  -- simp_rw [(DiscreteValuationRing.TFAE v.toSubalgebra h_field).out 0 1] -- failed to synthesize LocalRing ↥v.toSubalgebra
  -- infer_instance

open scoped IntermediateField

lemma findim (h : IsFunctionField F FF) {x : FF} (hx : ¬ IsAlgebraic F x) :
    FiniteDimensional F⟮x⟯ FF := by
  let ⟨v, h, h_unit⟩ := exists_place hx
  let v' := v.toValuationSubring.valuation
  wlog hx_pos : 0 < v' x generalizing x
  · sorry
  sorry

end IsFunctionField

end Place

--#min_imports
