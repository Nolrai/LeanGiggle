universe u

notation `rig` := semiring

def matrix (T) (n m : nat) := fin n -> fin m -> T

namespace matrix
section matrix

parameter T : Type u

infix `××`:20 := λ (n m : nat) T, matrix T n m

instance square_matrix_rig (n : nat) [T_rig : rig T] : rig ((n ×× n) T) :=
{
    add := matrix.add,
    one := λ n m, if n = m then 1 else 0,
    zero := λ _ _, 0,
}
