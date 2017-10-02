import .library.init.data.list


section defs

parameters (A : Type) [has_lt A]

inductive node (n : nat) : Type
| lit : A -> node
| var : forall m, m < n -> node

definition line n := list (node n)

inductive Grammar' : nat -> Type
| nil : Grammar' 0
| cons : forall n, line n -> Grammar' n -> Grammar' (nat.succ n)

local notation `GrammarS` n := (Grammar' (nat.succ n))

def startS : forall {n:nat}, (GrammarS n) -> option (line n) 
| (nat.succ n) (Grammar'.cons ._ l _) := option.some l
| 0 _ := none

def rulesS : forall {n}, (GrammarS n) -> Grammar' n
| ._ (Grammar'.cons n _ g) := g

local notation `Grammar` := Σ n, GrammarS n

def start : Grammar -> Σ n, line n 
| (sigma.mk ._ (Grammar'.cons n l _)) := sigma.mk n l

def rules : Grammar -> option Grammar 
| (sigma.mk (nat.succ n) (Grammar'.cons ._ _ g)) := some (sigma.mk n g)
| _ := none

def digram := prod A A

def digrams_naive : list A -> list digram
| [] := []
| (x::[]) := []
| (x::y::ys) := (x,y) :: digrams_naive (y::ys)

instance list_has_append (A : Type) : has_append (list A) :=
  has_append.mk list.append

universe u

instance type_prod : has_mul (Type u) := has_mul.mk prod

def split {T} (f : T -> bool) : list T -> ((list T) * (list T))
| [] := ([], [])
| (x::xs) :=
  if f x 
  then let (taken, after) := split xs in (x::taken, after)
  else ([], x::xs)

open list

theorem split_length 
  : forall l lx ly f
  , (lx, ly) = split f l -> lx ++ ly = l 
  := 
begin induction l
  , 
end


def group_by_eq {T} [ decidable_eq T ] : list T -> list (list T)
| [] := []
| (x::ys) := let (xs, ys') := split (= x) ys in 
have length ys' < length (x::ys), {apply split_length}
(x::xs) :: group_by_eq ys' 

def shrink_triples (l : list A) : list A := 
let shrink (xs : list A) := list.take 2 xs ++ list.drop 3 xs  in
list.bind (goup_by_eq l) shrink

def list_digrams : list A -> list digram := digrams_naive ∘ shrink_triples

def Grammar'_digrams {n : nat} : Grammar' n -> list digram

#check 1 + 2

end
