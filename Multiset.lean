import init.data.list

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

def first {α β γ : Type} : (α -> γ) -> (α * β) -> (γ * β)
| f (a, b) := (f a, b)

lemma eval_first {A B C} (f : A-> C) (a : A) (b : B) 
  : first f (a, b) = (f a, b) := 
  show (f a, b) = (f a, b), by reflexivity

def break {T} (f : T -> Prop) [forall x, decidable (f x)] 
  : list T -> ((list T) * (list T))
| [] := ([], [])
| (x::xs) :=
  if f x
  then ([], x::xs) 
  else first (λ xs', x::xs') (break xs)

def split {T} (f : T -> Prop) [forall x, decidable (f x)] := break (not ∘ f)

lemma ite_tt {A} {x y : A} : (if tt then x else y) = x :=
show x = x, {reflexivity}

lemma ite_then {A} {x y : A} {P : Prop} (p : P) [decidable P] 
  : (if P then x else y) = x :=
begin cases _inst_2
  , contradiction
  , unfold ite
end

lemma ite_ff {A} {x y : A} : (if ff then x else y) = y :=
show y = y, {reflexivity}

lemma ite_else {A} {x y : A} {P : Prop} (p : ¬ P) [decidable P] 
  : (if P then x else y) = y :=
begin cases _inst_2
  , unfold ite
  , contradiction
end

open tactic

def mapM {M} [monad M] {α β : Type} (f : α → M β)
  : list α -> M (list β)
| [] := pure []
| (x::xs) := (::) <$> f x <*> mapM xs

def mapM_ {M} [monad M] {α β : Type} (f : α → M β)
  : list α -> M unit
| [] := pure unit.star
| (x::xs) := f x >> mapM_ xs

meta def intro_inject  : tactic unit :=
  do 
    H <- mk_fresh_name >>= intro,
    parts <- injection H,
    mapM_ rewrite_target parts,
    mapM_ clear (H :: parts)

theorem break_preserves 
  {T} {f : T -> Prop} [forall x, decidable (f x)]
  : forall {l left_ right_ : list T}
  , (left_, right_) = break f l -> left_ ++ right_ = l
| [] := 
begin intros left_ right_
, unfold break
, intro_inject
, unfold has_append.append list.append
end
| (x :: xs) :=
begin intros left_ right_
, unfold break
, cases (_inst_2 x)
, rotate 1
, { rewrite ite_then
  , rotate 1, {exact a}
  , intro_inject
  , unfold has_append.append list.append
  }
, { rewrite ite_else
  , rotate 1, {exact a}
  , have H : exists fst snd, (fst, snd) = break f xs
  , { cases (break f xs)
    , split, rotate 1, exact fst
    , split, rotate 1, exact snd
    , reflexivity
    }
  , cases H 
  , cases a_2
  , rewrite <- a_3
  , rewrite eval_first
  , intro_inject
  , unfold has_append.append list.append
  , have H : a_1 ++ a_2 = xs
  , {apply break_preserves, assumption}
  , rewrite <- H
  , reflexivity 
  }
end

open list

lemma split_length_rest 
  {T} {f : T -> Prop} [forall x, decidable (f x)]
  : forall {l left_ right_ : list T}
  , (left_, right_) = split f l -> length right_ <= length l :=
begin intros
, rewrite <- (break_preserves 
end

def group_by_eq {T} [ decidable_eq T ] : list T -> list (list T)
| [] := []
| (x::ys) := let (xs, ys') := split (eq x) ys in 
have length ys' < length (x::ys), {apply split_length}
(x::xs) :: group_by_eq ys' 

def shrink_triples (l : list A) : list A := 
let shrink (xs : list A) := list.take 2 xs ++ list.drop 3 xs  in
list.bind (goup_by_eq l) shrink

def list_digrams : list A -> list digram := digrams_naive ∘ shrink_triples

def Grammar'_digrams {n : nat} : Grammar' n -> list digram

#check 1 + 2

end
