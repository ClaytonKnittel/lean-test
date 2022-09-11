
section ex1

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp,
end

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
      apply or.inl,
      apply and.intro,
        exact and.left h,
      exact hq,
    intro hr,
    apply or.inr,
    apply and.intro,
      exact and.left h,
    exact hr,
  intro h,
  apply or.elim h,
    intro hpq,
    apply and.intro,
      exact and.left hpq,
    apply or.inl,
    exact and.right hpq,
  intro hpr,
  apply and.intro,
    exact and.left hpr,
  apply or.inr,
  exact and.right hpr,
end

example (α : Type*) : α → α :=
begin
  intro a,
  exact a,
end

end ex1
