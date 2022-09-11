import tactic

section enum_types

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday


def number_of_day (d : weekday) : ℕ :=
  weekday.rec_on d 1 2 3 4 5 6 7
def number_of_day' (d : weekday) : ℕ :=
  weekday.cases_on d 1 2 3 4 5 6 7

#reduce number_of_day weekday.wednesday

namespace weekday

def next (d : weekday) : weekday :=
  weekday.cases_on d monday tuesday wednesday thursday
    friday saturday sunday

def previous (d : weekday) : weekday :=
  weekday.cases_on d saturday sunday monday tuesday
    wednesday thursday friday


example (d : weekday) : next (previous d) = d :=
  by apply weekday.cases_on d; refl

end weekday

end enum_types

section args

universes u v

inductive prod2 (α : Type u) (β : Type v)
| mk : α → β → prod2

inductive sum2 (α : Type u) (β : Type v)
| inl : α → sum2
| inr : β → sum2

def fst {α : Type u} {β : Type v} (p : α × β) : α :=
  prod.rec_on p (λ a b, a)

def snd {α : Type u} {β : Type v} (p : α × β) : β :=
  prod.rec_on p (λ a b, b)

def prod_example (p : bool × ℕ) : ℕ :=
  prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

#reduce prod_example (tt, 3)
#reduce prod_example (ff, 3)

def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
  sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)

#reduce sum_example (sum.inl 3)
#reduce sum_example (sum.inr 3)

inductive sum3 (α : Type u) (β : Type v)
| inl {} (a : α) : sum3
| inr {} (b : β) : sum3


-- defines constructor, mk, eliminators rec and rec_on,
-- and projections, fst and snd
structure prod4 (α β : Type*) :=
  mk :: (fst : α) (snd : β)

/-
structure Semigroup :=
  mk ::
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
-/
structure Semigroup :=
  (carrier : Type u)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

-- sigma types:
inductive sigma' {α : Type u} (β : α → Type v)
| dpair : Π a : α, β a → sigma'


inductive option' (α : Type*)
| none {} : option'
| some    : α → option'

-- example of a type class, i.e. lean can be instructed that
-- suitable base types are inhabited
inductive inhabited' (α : Type*)
| mk : α → inhabited'

end args

example : inhabited bool := inhabited.mk ff
example : inhabited ℕ := inhabited.mk 0

universes u v
example {α : Type u} {β : Type v} :
    (inhabited α) × (inhabited β) → inhabited (α × β) :=
  assume hinab : (inhabited α) × (inhabited β),
    inhabited.mk (prod.mk (hinab.fst).default (hinab.snd).default)

example {α : Type u} {β : Type v} :
    inhabited β → inhabited (α → β) :=
  assume h : inhabited β,
    inhabited.rec_on h (λ b, inhabited.mk (λ a, b))

#check exists.intro

inductive subtype' {α : Type*} (p : α → Prop)
| mk : Π x : α, p x → subtype'

section

variables {α : Type u} (p : α → Prop)

#check subtype p
#check { x : α // p x}

end

section defining_nat

inductive nat' : Type
| zero : nat'
| succ : nat' → nat'

#check @nat.rec_on


def add_nat (m n : ℕ) : ℕ :=
  nat.rec_on n m (λ n add_m_n, nat.succ add_m_n)

#reduce add_nat (nat.succ nat.zero) (nat.succ (nat.succ nat.zero))

/-
instance : has_zero nat := has_zero.mk zero
instance : has_add nat := has_add.mk add
-/
theorem zero_add (n : ℕ) : 0 + n = n :=
  @nat.rec_on (λ n : ℕ, 0 + n = n) n
    (show 0 + 0 = 0, from rfl)
    (assume n : ℕ,
      assume ih : 0 + n = n,
      show 0 + nat.succ n = nat.succ n, from
        calc
          0 + nat.succ n = nat.succ (0 + n) : rfl
          ...            = nat.succ n : by rw ih)

example (n : ℕ) : 0 + n = n :=
  nat.rec_on n rfl (λn ih, by rw [nat.add_succ, ih])
example (n : ℕ) : 0 + n = n :=
  nat.rec_on n rfl (λn ih, by simp only [nat.add_succ, ih])

theorem add_assoc (m n k : ℕ) : m + n + k = m + (n + k) :=
  nat.rec_on k
    (show m + n + 0 = m + (n + 0), from rfl)
    (assume k,
      assume ih : m + n + k = m + (n + k),
      show m + n + nat.succ k = m + (n + nat.succ k), from
        calc
          m + n + nat.succ k = nat.succ (m + n + k) : rfl
          ...                = nat.succ (m + (n + k)) : by rw ih
          ...                = m + nat.succ (n + k) : rfl
          ...                = m + (n + nat.succ k) : rfl)

example (m n k : ℕ) : m + n + k = m + (n + k) :=
  nat.rec_on k rfl (λ k ih, by simp only [nat.add_succ, ih])

theorem cons_append {α : Type*} (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

set_option pp.all true
#print cons_append
set_option pp.all false

-- def append {α : Type*} (s t : list α) : list α :=
--   list.rec t (λ x l u, x::u) s

theorem append_nil {α : Type*} (t : list α) : t ++ list.nil = t :=
  list.rec_on t
    (refl (list.nil ++ list.nil))
    (assume t, assume tl : list α,
      assume ih : tl ++ list.nil = tl,
      show (t :: tl) ++ list.nil = t :: tl, from
        calc
          (t :: tl) ++ list.nil = t :: (tl ++ list.nil) : list.cons_append t tl list.nil
          ...                   = t :: tl               : by rw ih)

theorem append_nil' {α : Type*} (t : list α) : t ++ list.nil = t :=
begin
  induction t,
  apply refl,
  simp [list.append, t_ih]
end

theorem append_assoc {α : Type*} (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) :=
    list.rec_on r
      (refl (list.nil ++ s ++ t))
      (assume rh, assume r,
        assume ih : r ++ s ++ t = r ++ (s ++ t),
        show (rh :: r) ++ s ++ t = (rh :: r) ++ (s ++ t), from
          calc
            (rh :: r) ++ s ++ t = rh :: (r ++ s) ++ t   : by rw list.cons_append
            ...                 = rh :: ((r ++ s) ++ t) : by rw list.cons_append
            ...                 = rh :: (r ++ (s ++ t)) : by rw ih)

def list_length {α : Type*} (l : list α) : ℕ :=
  list.rec_on l 0 (λ (hd : α) (l : list α) (ln : ℕ), ln + 1)


inductive binary_tree
| leaf : binary_tree
| node : binary_tree → binary_tree → binary_tree

inductive cbtree
| leaf : cbtree
| sup  : (ℕ → cbtree) → cbtree

def cbtree.succ (t : cbtree) : cbtree :=
  cbtree.sup (λ n, t)

def cbtree.omega : cbtree :=
  cbtree.sup (λ n, nat.rec_on n cbtree.leaf (λ n t, cbtree.succ t))

end defining_nat

section

theorem eq_trans {α : Type u} {a b c : α}
    (h1 : eq a b) (h2 : eq b c) : eq a c :=
  eq.subst h2 (eq.subst h1 (eq.refl a))

theorem eq_congr {α β : Type u} {a b : α} (f : α → β)
    (h : eq a b) : eq (f a) (f b) :=
  eq.rec_on h (eq.refl (f a))

end

section ex

def nat_pred (n : ℕ) : ℕ :=
  nat.rec_on n 0
    (λ n pred_n, nat.rec_on n 0
      (λ n' pred_n', nat.succ pred_n'))

def nat_mul (n m : ℕ) : ℕ :=
  nat.rec_on n 0 (λ n n_m, n_m + m)

def mul2 : nat → nat → nat
| 0 b     := 0
| (a+1) b := (mul2 a b) + b

def nat_sub (n m : ℕ) : ℕ :=
  nat.rec_on m n (λ m n_m, nat_pred n_m)

def nat_exp (n m : ℕ) : ℕ :=
  nat.rec_on m 1 (λ m n_m, nat_mul n n_m)

theorem pred_succ (n : ℕ) : nat.pred (n.succ) = n :=
  rfl

theorem nat_zero_mul (n : ℕ) : nat_mul 0 n = 0 := rfl

lemma succ_mul (n m : ℕ) : nat_mul n.succ m = nat_mul n m + m :=
  calc
    nat_mul n.succ m = nat_mul n m + m : rfl

theorem nat_mul_zero (n : ℕ) : nat_mul n 0 = 0 :=
  nat.rec_on n rfl (λ n ih,
    show nat_mul n.succ 0 = 0, from
      calc
        nat_mul n.succ 0 = nat_mul n 0 + 0 : succ_mul n 0
        ...              = 0 : ih)

theorem nat_mul_zero' (n : ℕ) : nat_mul n 0 = 0 :=
  nat.rec_on n rfl (λ n ih,
    show nat_mul n.succ 0 = 0, from
      (succ_mul n 0).trans ih)

end ex

section test

-- using library_search from "import tactic"
example (n : ℕ) : n + 1 > n :=
begin
  exact lt_add_one n,
end

example (n : ℕ) : nat.prime n → n ≥ 2 :=
begin
  exact nat.prime.two_le,
end

example (a b c : ℕ) : a + c < b + c → a < b :=
begin
  norm_num,
end

end test
