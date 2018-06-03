namespace preorder
section preorder
variable T : Type

def is_upper_bound [preorder T] : set T -> T -> Prop :=
    λ S x, ∀ y, y ∈ S -> y ≤ x

structure Op := op :: (unop : T)
variable {T}

def op (x : T) : Op T := Op.op x
def unop (x : Op T) : T := Op.unop x
def op_rel (R : T -> T -> Prop) (x y : Op T) := 
    R (unop y) (unop x)

def op_refl  
    {R : T -> T -> Prop} 
    (H : ∀ x : T, R x x)
    : (∀ x, op_rel R x x) 
:= begin unfold op_rel, exact (λ x, H (unop x)) end

def op_trans {R : T -> T -> Prop} 
    : transitive R -> transitive (op_rel R) :=
begin intros H a b c
, unfold op_rel
, intros 
, apply H
, all_goals {assumption}
end

def op_le [H : preorder T] := op_rel H.le

instance op_preorder [H : preorder T] : preorder (Op T) :=
{ le       := op_le
, le_refl  := op_refl H.le_refl 
, le_trans := op_trans H.le_trans 
}

variable {T}

def pointwise (R : T -> T -> Prop) {A} (f g : A -> T) :=
  ∀ x, R (f x) (g x) 

private def pointwise_relf 
  {R : T -> T -> Prop}
  (H : reflexive R) {A : Type} : reflexive (@pointwise _ R A) :=
  begin
  revert H,
  unfold reflexive pointwise,
  intros,
  apply H,
  end

private def pointwise_trans_helper 
    (R : T -> T -> Prop) (H : ∀ ⦃ x y z ⦄, R x y -> R y z -> R x z) 
    {A} {f h g : A -> T} 
    (FG : ∀ x, R (f x) (g x))
    (GH : ∀ x, R (g x) (h x)) 
    := λ (a : A), H (FG a) (GH a)

private def pointwise_trans
  {R : T -> T -> Prop}
  (H : transitive R) {A : Type}
  : @transitive (A → T) (@pointwise T R A) :=
  begin intros
  , unfold transitive pointwise at *
  , intros
  , apply (pointwise_trans_helper R H a a_1)
  end

instance pointwise_preorder {A : Type} [H : preorder T] 
  : preorder (A → T) :=
  { le := pointwise (λ a b, a ≤ b)
  , le_refl := begin apply (pointwise_relf H.le_refl) end
  , le_trans := pointwise_trans H.le_trans}

section functions_between
variables {A B : Type} [preorder A] [preorder B]
variables (f : A → B) (g : B -> A)

def monotonic :=
  ∀ x y, x ≤ y -> f x ≤ f y

variables (mf : monotonic f) (mg : monotonic g)

def are_adjoint := ∀ a b, f a ≤ b <-> a ≤ g b  

infix `⊢`:30 := are_adjoint

def equiv [preorder T] (a b : T) := (a ≤ b) ∧ (b ≤ a)

infix `≃`:50 := equiv
def injective [preorder T] (R : A -> T -> Prop) :=
∀ a b c, R a b -> R a c -> b ≃ c 

lemma right_adjoints_unique 
    : injective (@are_adjoint A B _ _) :=
    begin intros f g h
    , unfold are_adjoint
    , intros fg fh
    , split; intro
    ,   { rewrite ← fh, rewrite fg}
    ,   { rewrite ← fg, rewrite fh}
    end
lemma left_adjoints_unique : injective (λ x y, @are_adjoint B A _ _ y x) :=
    begin intros h f g
    , unfold are_adjoint
    , intros fh gh
    , split; intro
    ,   { rewrite fh, rewrite ← gh}
    ,   { rewrite gh, rewrite ← fh}
    end
end functions_between

definition bounds_above [preorder T] (S : set T) (x : T) : Prop := 
    ∀ y, y ∈ S → y ≤ x

definition bounds_below [preorder T] (S : set T) (x : T) : Prop :=
  ∀ y : T, y ∈ S -> x ≤ y 

end preorder
end preorder

open preorder

section
variable T : Type

def inclusion_trans 
(a b c : set T) 
(AB : a ⊆ b) 
(BC : b ⊆ c)
: a ⊆ c := λ t tInA, BC (AB tInA)

instance set_inclusion : preorder (set T) :=
{ preorder . le := set.subset 
, le_refl := λ A t inA, inA
, le_trans := inclusion_trans T
}

structure newtype (name : string) : Type :=
( old : T )

infix `!`:50 := newtype

structure equiv extends preorder T :=
    (symmetric : symmetric le)
 
structure partition := 
    (box : T -> set T)
    (correct : ∀ t s, t ∈ box s <-> box t = box s)

infix `⊞` : 60 := λ P x, partition.box P x

variable {T}

instance partition.part_box : has_coe_to_fun (partition T) 
    := 
    { F := λ _, T → set T
    , coe := λ (P : partition T) x, P ⊞ x }

-- Note the switch of P and Q.
def refined_by (P Q : partition T) : Prop := forall x, Q.box x ≤ P.box x 
def partition.indit (P : partition T) (x y : T) : Prop := y ∈ P x
def partition.dit (P : partition T) (x y : T) : Prop := y ∉ P x 

instance partition_refinement : preorder (partition T) := 
{ le := refined_by
, le_refl := λ _ _ _ H, H
, le_trans := λ _ _ _ f g t _ x, f t (g t x)
}

class has_meet (T : Type) := (meet : T -> T -> T)

def meet [m : has_meet T] (a b : T) : T := has_meet.meet a b
notation `⊻`:50 := meet -- lean uses ∨ for the or

class has_top (T : Type) := (top : T)
def top {T} [t : has_top T] : T := t.top

class meet_lattice (T : Type) extends preorder T, has_meet T, has_top T :=
    (meet_greater : ∀ a b z : T, z ≤ a -> z ≤ b -> z ≤ meet a b)
    (meet_less_l : ∀ a b, meet a b ≤ a)
    (meet_less_r : ∀ a b, meet a b ≤ b)
    (top_greater : ∀ a, a ≤ top)

class has_join (T : Type) := {join : T -> T -> T}

def join [m : has_join T] (a b : T) : T := has_join.join a b
notation `⊼`:50 := join -- lean uses ∧ for the and Proposition

class has_bottom (T : Type) := (bottom : T)
def bottom {T:Type} [has_bottom T] : T := @has_bottom.bottom T _

class join_lattice (T : Type) extends preorder T, has_join T, has_bottom T :=
    (join_less : ∀ a b z, a ≤ z → b ≤ z -> join a b ≤ z)
    (join_greater_l : ∀ a b, a ≤ join a b )
    (join_greater_r : ∀ a b, b ≤ join a b )
    (bottom_less : ∀ a , bottom ≤ a)

class lattice extends preorder T: Type :=
(to_meet_lattice : meet_lattice T)
(to_join_lattice : join_lattice T)

end
