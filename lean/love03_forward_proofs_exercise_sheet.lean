import .lovelib


/-! # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha : a,
show a, from ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha : a,
assume hb : b,
show b, from hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume hac : a → b → c,
assume hb : b,
assume ha : a,
show c, from
  hac ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume haa : a,
assume ha : a,
show a, from 
  ha

/-! Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
fix haa : a,
fix ha : a,
show a, from 
  ha

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume habc : a → b → c,
assume ha : a, 
assume hac : a → c,
assume hb : b,
show c, from 
  hac ha

/-! 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab : a → b,
assume hnb : ¬b,
assume ha : a,
show false, from
  hnb (hab ha)

/-! 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro (
  assume hall : ∀x, p x ∧ q x,
  have hpx : ∀x, p x :=
    fix x,
    and.elim_left (hall x),
  have hqx : ∀x, q x :=
    fix x,
    and.elim_right (hall x),
  show (∀x, p x) ∧ (∀x, q x), from 
    and.intro hpx hqx) 
  (
    assume handall: (∀x, p x) ∧ (∀x, q x),
    have hpx: ∀x, p x :=
      and.elim_left handall,
    have hqx: ∀x, q x :=
      and.elim_right handall,
    assume x : α,
    show p x ∧ q x, from
      and.intro (hpx x) (hqx x))

/-! 1.4 (**optional**). Reuse, if possible, the lemma `forall_and` from question
1.3 to prove the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
sorry

/-! 1.5. Supply a structured proof of the following property, which can be used
to pull a `∀`-quantifier past an `∃`-quantifier. -/

lemma forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
sorry


/-! ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry


/-! 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/-! 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  sorry
end


/-! ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

lemma proof_of_false :
  false :=
sorry

/-! 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false := 
sorry

end LoVe
