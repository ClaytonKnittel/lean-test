import data.int.basic

namespace test

variables (α β : Type*) (p q : α → Prop)
variables a b : α
variables f g : α → ℕ
variable h1 : a = b
variable h2 : f = g
variables x y z : ℕ

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  λ h : ∀ x : α, p x ∧ q x,
  λ y : α,
  (h y).left

example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
example : 2 + 3 = 5 := rfl

example (α : Type*) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
  eq.subst h1 h2
example (α : Type*) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example : f a = f b := congr_arg f h1
example : f a = g a := congr_fun h2 a
example : f a = g b := congr h2 h1

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
    from mul_add (x + y) x y,
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
    from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
  h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

theorem T2 (a b c d : ℕ)
    (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a   = b     : h1
    ... < b + 1 : nat.lt_succ_self b
    ... ≤ c + 1 : nat.succ_le_succ h2
    ... < d     : h3

example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y : by rw mul_add
    ... = x * x + y * x + (x + y) * y : by rw add_mul
    ... = x * x + y * x + (x * y + y * y) : by rw add_mul
    ... = x * x + y * x + x * y + y * y : by rw ←add_assoc

example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [mul_add, add_mul, add_mul, ←add_assoc]

example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [mul_add, add_mul, add_assoc, add_left_comm]


open nat

example : ∃ x : ℕ, x > 0 :=
  have h : 1 > 0, from zero_lt_succ 0,
  exists.intro 1 h

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
  exists.intro 0 h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
  exists.intro y (and.intro hxy hyz)

example : ∃ x : ℕ, x > 0 :=
  ⟨1, zero_lt_succ 0⟩


variable g2 : ℕ → ℕ → ℕ
variable hg2 : g2 0 0 = 0

theorem gex1 : ∃ x, g2 x x = x := exists.intro 0 hg2
theorem gex2 : ∃ x, g2 x 0 = x := exists.intro 0 hg2
theorem gex3 : ∃ x, g2 0 0 = x := exists.intro 0 hg2
theorem gex4 : ∃ x, g2 x x = 0 := exists.intro 0 hg2

set_option pp.implicit true
#print gex1
#print gex2
#print gex3
#print gex4

theorem T3 (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  exists.elim h
    (assume w : α,
      assume hw : p w ∧ q w,
      show ∃ x, q x ∧ p x, from
        exists.intro w (and.intro hw.right hw.left))

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with exists.intro (w : α) (hw : p w ∧ q w) :=
    exists.intro w (and.intro hw.right hw.left)
  end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hpw, hqw⟩ :=
    exists.intro w (and.intro hqw hpw)
  end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

-- implicit match
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

def is_even (a : ℕ) := ∃ b, a = 2 * b

theorem even_plus_even {a b : ℕ}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  exists.elim h1 (assume half_a : ℕ, assume hw1 : a = 2 * half_a,
  exists.elim h2 (assume half_b : ℕ, assume hw2 : b = 2 * half_b,
    exists.intro (half_a + half_b)
      (calc
        a + b = 2 * half_a + 2 * half_b : by rw [hw1, hw2]
          ... = 2 * (half_a + half_b)   : by rw mul_add)))

theorem even_plus_even' {a b : ℕ}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with ⟨w1, hw1⟩, ⟨w2, hw2⟩ :=
    ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
  end

end test

section exercises

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r :=
  (assume h : (∃ x : α, r),
    exists.elim h
    (assume a : α,
      (assume b : r, b)))
example (h : (∃ x : α, r)) : r :=
  match h with ⟨x, r⟩ :=
    r
  end

example (a : α) : r → (∃ x : α, r) :=
  (assume h : r, exists.intro a h)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume h : (∃ x, p x ∧ r),
      match h with ⟨x, hpx, hr⟩ :=
        ⟨⟨x, hpx⟩, hr⟩
      end)
    (assume h : (∃ x, p x) ∧ r,
      match h with ⟨⟨x, hpx⟩, hr⟩ :=
        ⟨x, hpx, hr⟩
      end)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
    (assume h : (∃ x, p x ∨ q x),
      match h with ⟨x, hpx_or_qx⟩ :=
        or.elim hpx_or_qx
          (assume hpx : p x, or.inl (exists.intro x hpx))
          (assume hqx : q x, or.inr (exists.intro x hqx))
      end)
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
      or.elim h
        (assume h1 : (∃ x, p x),
          match h1 with ⟨x, hpx⟩ :=
            ⟨x, or.inl hpx⟩
          end)
        (assume h2 : (∃ x, q x),
          match h2 with ⟨x, hqx⟩ :=
            ⟨x, or.inr hqx⟩
          end))


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  iff.intro
    (assume h : (∀ x, p x),
      (assume h2 : (∃ x, ¬ p x),
        match h2 with ⟨x, hnpx⟩ :=
          hnpx (h x)
        end))
    (assume h : ¬ (∃ x, ¬ p x),
      (assume x : α,
        by_contradiction
          (assume h2 : ¬ p x, h (exists.intro x h2))))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  iff.intro
    (assume h : (∃ x, p x),
      match h with ⟨x, hpx⟩ :=
        (assume h2 : ∀ x, ¬ p x, h2 x hpx)
      end)
    (assume h : ¬ (∀ x, ¬ p x),
      by_contradiction
        (assume h2 : ¬(∃ x, p x),
          have ∀ x, ¬p x, from
            (assume x : α, assume hpx : p x, h2 ⟨x, hpx⟩),
          h this))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (assume h : (¬ ∃ x, p x),
      (assume x : α, assume hpx : p x, h ⟨x, hpx⟩))
    (assume h : (∀ x, ¬ p x),
      assume h2 : ∃ x, p x,
        match h2 with ⟨x, hpx⟩ :=
          h x hpx
        end)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (assume h : (¬ ∀ x, p x),
      by_contradiction
        (assume h2 : (¬ ∃ x, ¬ p x),
          have ∀ x, p x, from
            (assume x : α,
              by_contradiction
                (assume h3 : ¬ p x,
                  h2 ⟨x, h3⟩)),
          show false, from h this))
    (assume h : (∃ x, ¬ p x),
      match h with ⟨x, hnpx⟩ :=
        (assume h2 : ∀ x, p x, hnpx (h2 x))
      end)

end exercises