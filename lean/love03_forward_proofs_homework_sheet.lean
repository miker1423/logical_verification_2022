import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
assume dn : double_negation,
have em: excluded_middle := 
  sorry_lemmas.em_of_dn dn,
peirce_of_em em

lemma em_of_peirce :
  peirce → excluded_middle :=
assume p : peirce,
have dn : double_negation :=
  dn_of_peirce p,
sorry_lemmas.em_of_dn dn


lemma dn_of_em :
  excluded_middle → double_negation :=
assume em : excluded_middle,
have pe : peirce :=
  peirce_of_em em,
dn_of_peirce pe

end backward_proofs

/-! 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
iff.intro (
  assume hepxaqx : ∃x, p x ∧ q x,
  show ∃x, q x ∧ p x, from
    exists.elim hepxaqx
    (
      fix x : α,
      assume pxaqx : p x ∧ q x,
      have hpx : p x := and.elim_left pxaqx,
      have hqx : q x := and.elim_right pxaqx,
      exists.intro x (and.intro hqx hpx)
    )
) (
  assume hqxapx : ∃x, q x ∧ p x,
  show ∃x, p x ∧ q x, from
    exists.elim hqxapx
    (
      fix x : α,
      assume qxapx : q x ∧ p x,
      have hqx : q x := and.elim_left qxapx,
      have hpx : p x := and.elim_right qxapx,
      exists.intro x (and.intro hpx hqx)
    )
)


/-! ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied Logic and Sets with Prof. Fokkink, you will know he is fond
of logic puzzles. This question is a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/-! 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

/- Reuse of lamba from HW 1 as proof term. -/
lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b: Prop,
λf, f (λab, ab (λaa, f (λ_, aa)))

/-! 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b : Prop,
assume habaab : (((a → b) → a) → a) → b,
show b, from
  habaab (  
    assume habaa : (a → b) → a,
    show a, from 
      habaa (
        assume ha,
        show b, from 
          habaab (
            assume haba : (a → b) → a,
            ha
          )
      )
  )

end LoVe
