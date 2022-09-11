
section s1

structure point (α : Type*) :=
  mk :: (x : α) (y : α)

namespace point

def add (p q : point ℕ) : point ℕ := mk (p.x + q.x) (p.y + q.y)

end point

#check point
#check point.rec_on
#check point.x
#check point.y

-- print all generated constructions
#print prefix point

#reduce point.x (point.mk 10 20)
#reduce (point.mk 10 20).y

example (α : Type*) (a b : α) :
    point.x (point.mk a b) = a :=
  eq.refl a

-- inline-declared universe u
structure {u} produc (α : Type u) (β : Type u) : Type u :=
  (pr1 : α) (pr2 : β)


#check { point . x := 10, y := 20 } -- point ℕ
#check ({x := 10, y := 20} : point ℕ)

-- update only some fields of a structure
def p : point ℕ := {x := 1, y := 2}
#reduce {y := 3, ..p}


inductive color
  | red
  | green
  | blue

structure color_point (α : Type*) extends point α :=
  mk :: (c : color)

#reduce color_point.mk {x := 10, y := 20} color.red

end s1
