open classical
open function

definition is_lower_bound_of {T} [preorder T] (S : set T) (x : T) : Prop :=
    ∀ y, y ∈ S → x ≤ y

definition is_upper_bound_of {T} [preorder T] (S : set T) (x : T) : Prop :=
    ∀ y, y ∈ S → y ≤ x

definition is_greatest_of {T} [preorder T] (S : set T) (x : T) : Prop :=
x ∈ S ∧ is_upper_bound_of S x

definition is_least_of {T} [preorder T] (S : set T) (x : T) : Prop :=
x ∈ S ∧ is_lower_bound_of S x

class lattice (T : Type) extends partial_order T :=
  (sup 
  : ∀ s : ℕ → T, ∃! x : T, 
  (is_least_of 
    (set_of (is_upper_bound_of (λ x, ∃ n, x = s n))) 
    x)
  )



namespace enriched
end enriched
