
open function

structure distinct (size : ℕ) (α : Type) : Type :=
    (f : fin size → α)
    (injective : injective f)

namespace distinct
section
parameter {size : ℕ}
parameter {α : Type}
definition to_set (d : distinct size α) : set α :=
    λ a : α, ∃ i, d.f i = a

instance distinct_has_coe : has_coe (distinct size α) (set α)
    := has_coe.mk to_set  
end

namespace unordered
section
open fin
open distinct
parameter size : ℕ
parameter α : Type

open function.equiv

private definition eqv (d0 d1 : distinct size α) : Prop :=
    d0.to_set = d1.to_set

private lemma eqv_is_equiv : equivalence eqv :=
    begin repeat {split}
        ; unfold reflexive symmetric transitive eqv
        ; intro x
    , {reflexivity}
    , {intros y h, symmetry, exact h}
    , {intros y z xy yz, transitivity (to_set y); assumption}
    end

instance setoid : setoid (distinct size α) :=
    setoid.mk _ eqv_is_equiv

definition unordered : Type := quotient setoid
end

section
parameter {size : ℕ}
parameter {α : Type}
definition to_set_respects 
    : ∀ a b : (distinct size α), a ≈ b → to_set a = to_set b :=
    begin intros a b h
    , unfold has_equiv.equiv setoid.r eqv at h
    , exact h
    end

definition to_set := quotient.lift to_set to_set_respects
end

instance has_lift (n : ℕ) (α : Type) 
    : has_lift (unordered n α) (set α) :=
has_lift.mk to_set 

end unordered

definition unordered := unordered.unordered 
end distinct
open distinct.unordered

namespace line_geometry
section
notation `double` a :100 := (unordered 2 a : Type)
open distinct
parameters (Point Line : Type)

class line_geometry
    [has_lift Line (set Point)] :=
    mk ::
    (fixed_by : double Point → Line)
    (fixed_by_correct 
        : ∀ (pt : double Point) (l : Line), 1 ≤ 2)

end
end line_geometry

namespace curve_geometry
section
notation `tripple` a :100 := (unordered 3 a : Type)
open distinct
parameters (Point Curve : Type)
class curve_geometry 
    [has_lift Curve (set Point)] :=
    (fixed_by : tripple Point → Curve)
    (fixed_by_correct 
        : ∀ (pt : tripple Point) (c : Curve)
            , ↑pt ⊆ (↑c : set Point) ↔ c = fixed_by pt)

end
end curve_geometry

notation `curve_geometry` := curve_geometry.curve_geometry

