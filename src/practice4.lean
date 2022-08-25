import data.int.basic
import data.nat.basic
import data.real.basic

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


-- if, for all x, p x implies r, then if there exists
-- an x such that p x, r is true, and vice versa
example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    (assume h : (∀ x, p x → r),
      (assume hx : (∃ x, p x),
        match hx with ⟨x, hpx⟩ :=
          h x hpx
        end))
    (assume h : (∃ x, p x) → r,
      (assume x : α,
        assume hpx : p x,
          h (exists.intro x hpx)))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (assume h : (∃ x, p x → r),
      (assume h2 : (∀ x, p x),
        match h with ⟨x, hpx_to_r⟩ :=
          hpx_to_r (h2 x)
        end))
    (assume h : (∀ x, p x) → r,
      by_contradiction
        (assume h2 : ¬(∃ x, p x → r),
          have ∀ x, ¬(p x → r), from
            (assume x : α, assume hpxr : p x → r,
              h2 (exists.intro x hpxr)),
          have h3 : ∀ x, p x ∧ ¬r, from
            (assume x : α, not_imp.mp (this x)),
          have ∀ x, p x, from
            (assume x : α, (h3 x).left),
          show false, from (h3 a).right (h this)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (assume h : (∃ x, r → p x),
      match h with ⟨x, r_imp_px⟩ :=
        assume hr : r,
          exists.intro x (r_imp_px hr)
      end)
    (assume h : r → (∃ x, p x),
      by_contradiction
        (assume h2 : ¬(∃ x, r → p x),
          have ∀ x, ¬(r → p x), from
            forall_not_of_not_exists h2,
          have ∀ x, r ∧ ¬ p x, from
            (assume x : α, not_imp.mp (this x)),
          have r ∧ ∀ x, ¬ p x, from
            (and.intro (this a).left (assume x, (this x).right)),
          match (h this.left) with ⟨x, hpx⟩ :=
            (this.right x) hpx
          end))

end exercises

section exercises2

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  iff.intro
    (assume : (∀ x, p x ∧ q x),
      and.intro
        (assume x, (this x).left)
        (assume x, (this x).right))
    (assume : (∀ x, p x) ∧ (∀ x, q x),
      (assume x,
        and.intro (this.left x) (this.right x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (assume h : ∀ x, p x → q x,
    (assume hp : ∀ x, p x,
      assume x, (h x) (hp x)))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (assume : (∀ x, p x) ∨ (∀ x, q x),
    or.elim this
      (assume : ∀ x, p x, assume x, or.inl (this x))
      (assume : ∀ x, q x, assume x, or.inr (this x)))


example : α → ((∀ x : α, r) ↔ r) :=
  (assume a : α,
    iff.intro
      (assume h : ∀ x, r, h a)
      (assume h : r, assume x, h))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (assume h : ∀ x, p x ∨ r,
      or.elim (em r)
        (assume hr : r, or.inr hr)
        (assume hnr : ¬r, or.inl
          (assume x, or.elim (h x)
            (assume : p x, this)
            (assume : r, absurd this hnr))))
    (assume h : (∀ x, p x) ∨ r,
      or.elim h
        (assume : ∀ x, p x, assume x, or.inl (this x))
        (assume : r, assume x, or.inr this))


variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  have barber_doesnt_shave_self : ¬ shaves barber barber, from
    (assume : shaves barber barber, absurd this ((h barber).mp this)),
  absurd ((h barber).mpr barber_doesnt_shave_self) barber_doesnt_shave_self


def divides (m n : ℕ) : Prop := ∃ k : ℕ, m * k = n
def even (n : ℕ) : Prop := ∃ k : ℕ, 2 * k = n

def prime (n : ℕ) : Prop := ¬∃ k : ℕ, k > 1 ∧ k ≠ n ∧ divides k n

def infinitely_many_primes : Prop :=
  ∀ n : ℕ, ∃ p : ℕ, p > n ∧ prime p

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ k : ℕ, k > 0 ∧ n = 2 ^ k + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : ℕ, ∃ p : ℕ, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, (n > 2 ∧ even n) → ∃ k j : ℕ, (prime k ∧ prime j ∧ n = k + j)

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : ℕ, (n > 5 ∧ ¬ even n) → ∃ k j i : ℕ, (prime k ∧ prime j ∧ prime i ∧ n = k + j + i)

def Fermat's_last_theorem : Prop :=
  ∀ n : ℕ, (n > 2) → ¬∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ (a ^ n + b ^ n = c ^ n)


theorem inf_primes : infinitely_many_primes :=
  have prime 2, from
    have ∀ k : ℕ, k ≤ 1 ∨ k = 2 ∨ ¬ divides k 2, from
      (assume k, or.elim (em (k ≤ 1))
        (assume : k ≤ 1, or.inl this)
        (assume k_lt_1 : ¬(k ≤ 1), or.inr (or.elim (em (k = 2))
          (assume : k = 2, or.inl this)
          (assume : k ≠ 2,
            have k > 1, from
              lt_of_not_ge k_lt_1,
            have k > 2, from
              sorry,
            have ¬divides k 2, from
              sorry,
            or.inr this)))),
    sorry,
  sorry


variables log exp    : ℝ → ℝ
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : ℝ) :
  exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

example (y : ℝ) (h : y > 0) : exp (log y) = y :=
  exp_log_eq h

theorem log_mul {x y : ℝ} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
  calc
    log (x * y) = log (exp (log x) * y)           : by rw exp_log_eq hx
    ...         = log (exp (log x) * exp (log y)) : by rw exp_log_eq hy
    ...         = log (exp (log x + log y))       : by rw exp_add
    ...         = log x + log y                   : by rw log_exp_eq


example (x : ℤ) : x * 0 = 0 :=
  calc
    x * 0 = x * (x - x)   : by rw sub_self x
    ...   = x * x - x * x : by rw mul_sub x x x
    ...   = 0             : by rw sub_self (x * x : ℤ)

end exercises2
