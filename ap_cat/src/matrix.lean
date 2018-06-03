universe u



inductive Fin : nat -> Type
| zero : ∀ n, Fin (nat.succ n)
| succ : ∀ n, Fin n -> Fin (nat.succ n) 

def Fin.mk (n : nat) {m : nat} : (m ≤ n) ⊕ Fin m : 

class strong_finite (X : Type u)  :=
    (list_all : list X)
    (is_all : ∀ x : X, x ∈ list_all)

def list_all {T} [h : strong_finite T] := h.list_all

def fin.list_all : Π {n : nat}, list (fin n)
| 0 := []
| (nat.succ n) := 0 :: list.map fin.succ fin.list_all

def fin_induction 
    (C : Π {n}, fin n -> Type u)
    (Z : Π {n} (Z_ih : Π f : fin n, C f), C (0 : fin (nat.succ n)))
    (S : Π {n} (f : fin n) (S_ih : C f), C (fin.succ f))
    : Π n (f : fin n), C f :=
begin intros,
    induction f; induction n; induction f_val,
    apply Z,
end

instance fin_finite : strong_finite (fin n) 

end fin

notation `rig` := semiring

section matrix

parameter T : Type u
def matrix (n m : nat) := fin n -> fin m -> T

local infix `▪`:20 := λ (n m : nat), matrix n m

def matrix.add {n m} (a b : n ▪ m) [has_add T] : n ▪ m :=
λ x y, (a x y) + (b x y)

def sumup {A B} (f : A -> B) [rig B] : list A -> B := list.foldr (λ r l, f r + l) 0

def matrix.comp {n k m} (a : n ▪ k) (b : k ▪ m) [has_add T] : n ▪ m :=
λ x y, sumup (list_all k)

instance square_matrix_rig (n : nat) [T_rig : rig T] : rig (n ▪ n) :=
{
    add := λ a b, matrix.add a b,
    one := λ n m, if n = m then 1 else 0,
    zero := λ _ _, 0,
}
