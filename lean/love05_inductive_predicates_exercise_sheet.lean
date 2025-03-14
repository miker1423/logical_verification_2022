import .love05_inductive_predicates_demo


/-! # LoVe Exercise 5: Inductive Predicates -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Even and Odd

The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/-! We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/-! 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases'` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
begin
  rw odd,
  intro h,
  induction' h,
end

/-! 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here
lemma odd_3 :
  odd 3 :=
begin 
  intro h,
  cases' h,
  apply odd_1,
  assumption,
end

lemma odd_5 : 
  odd 5 :=
begin
  intro h,
  cases' h,
  apply odd_3,
  assumption,
end

/-! 1.3. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
begin 
  induction' m,
  { simp,
    apply even.add_two,
    apply even.zero, },
  { 
    apply even.add_two,
    apply ih,
  }
end

/-! 1.4. Complete the following proof by rule induction.

Hint: You can use the `cases'` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m :=
begin
  intros n hen,
  induction' hen,
  case zero {
    apply exists.intro 0,
    refl },
  case add_two : k hek ih {
    cases' ih,
    apply exists.intro (w + 1),
    rw h,
    linarith,
  }
end

/-! 1.5. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
begin
  apply iff.intro,
  {
    apply even_imp_exists_two_times,
  },
  {
    intro he,
    cases' he,
    rw [h],
    apply even_two_times,
  }
end

/-! 1.6 (**optional**). Give a structurally recursive definition of `even` and
test it with `#eval`.

Hint: The negation operator on `bool` is called `not`. -/

def even_rec : nat → bool :=
sorry


/-! ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check score

/-! 2.1. Define an inductive predicate that returns true if the server is ahead
of the receiver and that returns false otherwise. -/

inductive srv_ahead : score → Prop
-- enter the missing cases here

/-! 2.2. Validate your predicate definition by proving the following lemmas. -/

lemma srv_ahead_vs {m n : ℕ} (hgt : m > n) :
  srv_ahead (score.vs m n) :=
sorry

lemma srv_ahead_adv_srv :
  srv_ahead score.adv_srv :=
sorry

lemma not_srv_ahead_adv_rcv :
  ¬ srv_ahead score.adv_rcv :=
sorry

lemma srv_ahead_game_srv :
  srv_ahead score.game_srv :=
sorry

lemma not_srv_ahead_game_rcv :
  ¬ srv_ahead score.game_rcv :=
sorry

/-! 2.3. Compare the above lemma statements with your definition. What do you
observe? -/

-- enter your answer here


/-! ## Question 3: Binary Trees

3.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

#check is_full_mirror
#check mirror_mirror

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
sorry

/-! 3.2. Define a `map` function on binary trees, similar to `list.map`. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| _ := sorry   -- remove this dummy case and enter the missing cases

/-! 3.3. Prove the following lemma by case distinction. -/

lemma map_btree_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : btree α, map_btree f t = btree.empty ↔ t = btree.empty :=
sorry

/-! 3.4 (**optional**). Prove the following lemma by rule induction. -/

lemma map_btree_mirror {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (map_btree f t) :=
sorry

end LoVe
