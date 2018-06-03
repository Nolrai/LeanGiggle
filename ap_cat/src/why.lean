universes u v

inductive why (P : Prop) (L : Type u) (R : Type v)  
| inL {} : P -> L -> why 
| inR {} : ¬ P -> R -> why

inductive option_why (P : Prop) (T : Type v)
| none {} : P -> option_why
| some {} : ¬ P -> T -> option_why

section
parameters {P : Prop}
parameters {R : Type u}

def option_why.to_why: option_why P R -> why P unit R
| (option_why.none p) := why.inL p () 
| (option_why.some p r) := why.inR p r

def option_why.to_why_coe
    : has_coe (option_why P R) (why P unit R) :=
    ⟨option_why.to_why⟩

open option_why

def option_why.map
    {P : Prop}
    {A : Type u} {B : Type v} 
    (f : A -> B) 
    : option_why P A -> option_why P B 
| (none p) := option_why.none p
| (some p a) := some p (f a)

instance option_why.functor {P} : functor (option_why P) :=
{map := @option_why.map P}

end