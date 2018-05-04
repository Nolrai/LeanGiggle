universe u

def vacuous {T:Sort u} (e : empty) : T := 
match e with
end

def one : preorder unit :=
{ le := λ _ _, true
, le_refl := by intro; split
, le_trans := by intros; split}

def set_inclusion (T : Type) : preorder (set T) :=
{ preorder . O := set T
, R := set.subset 
, id := λ _ _ H, H
, comp := λ _ _ _ f g _ inA, f (g inA)
}

section
variable T : Type

structure partition := (box : T -> set T) (correct : ∀ t s, t ∈ box s <-> box t = box s)
variable {T}

instance partition.part_box : has_coe_to_fun (partition T) 
    := { F := λ _, T → set T, coe := λ (p : partition T), partition.box p }

definition partition.dit (P : partition T) (s t : T) : Prop := t ∉ P s

def refined_by (P Q : partition T) := ∀ s t, partition.dit P s t -> partition.dit Q s t

instance partition_ : preorder (partition T) := 
{ le := refined_by
, le_refl := \l}
