universe u

def one : preorder unit :=
{ le := λ _ _, true
, le_refl := by intro; split
, le_trans := by intros; split}

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

structure partition := 
    (box : T -> set T)
    (correct : ∀ t s, t ∈ box s <-> box t = box s)

variable {T}

instance partition.part_box : has_coe_to_fun (partition T) 
    := { F := λ _, T → set T, coe := λ (p : partition T), partition.box p }

-- Note the switch of P and Q.
def refined_by (P Q : partition T) : Prop := forall x, Q.box x ≤ P.box x  
def partition.indit (P : partition T) (x y : T) : Prop := P x = P y
def partition.dit (P : partition T) (x y : T) : Prop := P x ≠ P y 

instance partition_refinement : preorder (partition T) := 
{ le := refined_by
, le_refl := λ _ _ _ H, H
, le_trans := λ _ _ _ f g t _ x, f t (g t x)
}



end