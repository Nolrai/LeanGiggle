structure category_raw  :=
(Ob: Type) (Hom : Ob -> Ob -> Type)
(id : ∀ A : Ob, Hom A A)
(comp : ∀ (A B C : Ob), Hom A B -> Hom B C -> Hom A C)

notation A `♯` c `⟹`:50 B := c.Hom A B  

definition comp {c : category_raw}
    {A B C : c.Ob}
    (f : A ♯c⟹ B)
    (g : B ♯c⟹ C)
    := c.comp A B C f g


open category_raw
infix `#`:700 := comp
        
structure category extends category_raw :=
(raw := to_category_raw)
(left_unit 
    : ∀ A B (f : A ♯ raw ⟹ B)
    ,  f = f # (id B) )
(right_unit 
    : ∀ A B (f : A ♯ raw ⟹ B)
    ,  f = (id A) # f)
(comp_associtive 
    : ∀ A B C D 
        (f : A ♯ to_category_raw ⟹ B)
        (g : B ♯ to_category_raw ⟹ C)
        (h : C ♯ to_category_raw ⟹ D)
    , (f # g) # h = f # (g # h)
)

