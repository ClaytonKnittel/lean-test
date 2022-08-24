
def zero : (ℕ → ℕ) → ℕ := λf, f 0

#check zero
#print zero

#reduce zero (λn, n + 1)


namespace test

universe u
constant cons   : Π {α : Type u}, α → list α → list α
constant nil    : Π {α : Type u}, list α
constant head   : Π {α : Type u}, list α → α
constant tail   : Π {α : Type u}, list α → list α
constant append : Π {α : Type u}, list α → list α → list α


variable α : Type
variable a : α
variables l1 l2 : list α

#check cons a nil
#check append (cons a nil) l1

#check nil

end test


def double (x : ℕ) : ℕ := x + x
#print double
#check double 3
#reduce double 3    -- 6

def square (x : ℕ) := x * x
#print square
#check square 3
#reduce square 3    -- 9

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

#reduce do_twice double 2

def quad (x : ℕ) := do_twice double x
def oct  (x : ℕ) := double (do_twice double x)

namespace hidden

def curry {α β γ : Type*} (f : α × β → γ) : α → β → γ := λa, λb, f (a, b)
def uncurry {α β γ : Type*} (f : α → β → γ) : α × β → γ := λab, f ab.1 ab.2

def mult (x y : ℕ) : ℕ := x * y
def dot  (xy : (ℕ × ℕ)) : ℕ := xy.1 * xy.2

#reduce uncurry mult (2, 3)
#reduce curry dot 2 3

end hidden



universe u
constant vec : Type u → ℕ → Type u

namespace vec
constant empty : Π α : Type u, vec α 0
constant cons :
  Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
constant append :
  Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
constant vec_add :
  Π {α : Type u} (n : ℕ), vec α n → vec α n → vec α n
constant vec_reverse :
  Π {α : Type u} (n : ℕ), vec α n → vec α n
constant rev2 {α : Type u} (n : ℕ) : vec α n → vec α n


#check empty
#check append ℕ 2 3
#check vec_add 5
#check vec_reverse 10
#check rev2 10

end vec
