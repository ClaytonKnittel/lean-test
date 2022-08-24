
namespace test

constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

constant Proof : Prop -> Type
constant and_comm : Π p q : Prop,
  Proof (implies (and p q) (and q p))

variables p q : Prop
#check and_comm p q


constant modus_ponens :
  Π p q : Prop, Proof (implies p q) → Proof p → Proof q

constant implies_intro :
  Π p q : Prop, (Proof p → Proof q) → Proof (implies p q)

end test

namespace test2

constants p q : Prop

-- theorem and lemma are identical, and are
-- equivalent to definitions
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
theorem t2 : p → q → p :=
  assume hp : p,
  assume hq : q,
  show p, from hp
theorem t3 (hp : p) (hq : q) : p := hp

-- axiom is equivalent to constant
axiom hp : p
theorem t4 : q → p := t1 hp

-- ∀ is equivalent to Π
theorem t5 (p q : Prop) (hp : p) (hq : q) : p := hp
theorem t6 : ∀ (p q : Prop), p → q → p :=
  λ (p q : Prop) (hp : p) (hq : q), hp

-- variables are auto-generalized in theorems
variables p q : Prop
theorem t7 : p → q → p := λ (hp : p) (hq : q), hp

-- the assumption that p holds
variable hp : p
theorem t8 : q → p := λ (hq : q), hp

variables r s : Prop

theorem t9 (h₁ : q → r) (h₂ : p → q) : p → r :=
  assume h₃ : p,
  show r, from h₁ (h₂ h₃)


-- example is a theorem without naming or
-- storing in the permanent context
example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq

-- and elimination
example (h : p ∧ q) : p := and.elim_left h
example (h : p ∧ q) : q := and.elim_right h

-- and is isomorphic to × (product type)
example (hpq : p ∧ q) : q ∧ p :=
  and.intro (and.right hpq) (and.left hpq)


-- or introduction
example (hp : p) : p ∨ q := or.intro_left q hp
example (hq : q) : p ∨ q := or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  or.elim h
    (λ hp : p,
      show q ∨ p, from or.intro_right q hp)
    (λ hq : q,
      show q ∨ p, from or.intro_left p hq)

-- or.inr is shorthand for or.intro_right _
-- or.inl is shorthand for or.intro_left _
example (h : p ∨ q) : q ∨ p :=
  or.elim h
    (λ hp : p,
      show q ∨ p, from or.inr hp)
    (λ hq : q,
      show q ∨ p, from or.inl hq)

-- negation is defined as ¬p = p → false
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  assume hp : p,
  show false, from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q :=
  false.elim (hnp hp)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- false only has an elimination rule, false → anything
-- true only has an introduction rule, true.intro : true

theorem and_swap : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume h : p ∧ q,
      show q ∧ p, from and.intro h.right h.left)
    (assume h : q ∧ p,
      show p ∧ q, from and.intro h.right h.left)

definition and_swap' : iff (and p q) (and q p) :=
  iff.intro
    (λ h : and p q, and.intro h.right h.left)
    (λ h : and q p, and.intro h.right h.left)

theorem and_swap'' : p ∧ q ↔ q ∧ p :=
  ⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩

section
example (h : p ∧ q) : q ∧ p := iff.mpr (and_swap q p) h
example : p ∧ q → q ∧ p := λ h : p ∧ q, iff.mpr (and_swap q p) h

example (h : p ∧ q) : q ∧ p :=
  have hp : p, from and.left h,
  have hq : q, from and.right h,
  show q ∧ p, from and.intro hq hp

example : p ∧ q → q ∧ p :=
  λ h : p ∧ q,
    (λ hp : p, λ hq : q, and.intro hq hp)
    (and.left h) (and.right h)

-- can reason backwards with suffices, i.e. if we show q,
-- then we have proved it, and next we show q
example (h : p ∧ q) : q ∧ p :=
  have hp : p, from h.left,
  suffices hq : q, from and.intro hq hp,
  show q, from h.right

end


section
open classical

-- p ∨ ¬p
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)

theorem dne' {p : Prop} (h : ((p → false) → false)) : p :=
  or.elim (em p)
    (λ hp : p, hp)
    (λ hnp : p → false, absurd hnp h)

/-
 - Assume ¬(p ∨ ¬p), then ¬p, since p → (p ∨ ¬p) → false.
 - However, ¬p → (p ∨ ¬p) → false, so we have a contradiction.
 - ∴ dne ¬¬(p ∨ ¬p)
 -/
theorem em' {p : Prop} : p ∨ ¬p :=
  dne (
    assume h : ¬(p ∨ ¬p),
    have hnp : ¬p, from (
      assume hp : p,
      show false, from h (or.inl hp)
    ),
    show false, from h (or.inr hnp))

theorem em'' {p : Prop} : p ∨ ¬p :=
  dne (
    λ h : (p ∨ ¬p) → false,
      h (or.inr (λ hp : p, h (or.inl hp)))
  )

def double (x : ℕ) : ℕ := x + x
def double' : ℕ → ℕ := λ (x : ℕ), x + x

example (h : ¬¬p) : p :=
  by_cases
    (λ h1 : p, h1)
    (λ h2 : ¬p, absurd h2 h)

example (h : ¬¬p) : p :=
  by_contradiction
    (λ hnp : ¬p, absurd hnp h)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  or.elim (em p)
    (λ hp : p, or.inr (λ hq : q, h (and.intro hp hq)))
    (λ hnp : ¬p, or.inl hnp)

end

section

example {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (λ h : p ∧ (q ∨ r),
      or.elim h.elim_right
        (λ hq : q, or.inl (and.intro h.elim_left hq))
        (λ hr : r, or.inr (and.intro h.elim_left hr)))
    (λ h : (p ∧ q) ∨ (p ∧ r),
      or.elim h
        (λ hpq : p ∧ q, and.intro hpq.left (or.inl hpq.right))
        (λ hpr : p ∧ r, and.intro hpr.left (or.inr hpr.right)))

example : ¬(p ∧ ¬q) → (p → q) :=
  assume h : ¬(p ∧ ¬q),
  assume hp : p,
  show q, from
    or.elim (classical.em q)
      (assume hq : q, hq)
      (assume hnq : ¬q, absurd (and.intro hp hnq) h)

end

section exercises

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume hpq : p ∧ q, and.intro hpq.right hpq.left)
    (assume hqp : q ∧ p, and.intro hqp.right hqp.left)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume hpq : p ∨ q, or.elim hpq
      (assume hp : p, or.inr hp)
      (assume hq : q, or.inl hq))
    (assume hqp : q ∨ p, or.elim hqp
      (assume hq : q, or.inr hq)
      (assume hp : p, or.inl hp))


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume h : (p ∧ q) ∧ r,
      and.intro h.left.left (and.intro h.left.right h.right))
    (assume h : p ∧ (q ∧ r),
      and.intro (and.intro h.left h.right.left) h.right.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume h : (p ∨ q) ∨ r,
      or.elim h
        (assume hpq : p ∨ q,
          or.elim hpq
            (assume hp : p, or.inl hp)
            (assume hq : q, or.inr (or.inl hq)))
        (assume hr : r, or.inr (or.inr hr)))
    (assume h : p ∨ (q ∨ r),
      or.elim h
        (assume hp : p, or.inl (or.inl hp))
        (assume hqr : q ∨ r,
          or.elim hqr
            (assume hq : q, or.inl (or.inr hq))
            (assume hr : r, or.inr hr)))


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry

example {p : Prop} : ¬(p ↔ ¬p) :=
  λ h : p ↔ ¬p, or.elim (classical.em p)
    (assume hp : p, absurd hp ((iff.mp h) hp))
    (assume hnp : ¬p, absurd ((iff.mpr h) hnp) hnp)

example {p : Prop} : ¬(p ↔ ¬p) :=
  assume h : p ↔ ¬p,
  have hnp : ¬p, from
    (assume hp : p,
      absurd hp (iff.mp h hp)),
  have hp : p, from
    (iff.mpr h hnp),
  show false, from hnp hp

example {p : Prop} : ¬(p ↔ ¬p) :=
  λ h : p ↔ ¬p,
  have hnp : ¬p, from
    (λ hp : p, absurd hp (iff.mp h hp)),
  hnp (iff.mpr h hnp)

end exercises

end test2
