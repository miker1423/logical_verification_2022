import .love07_metaprogramming_demo


/-! # LoVe Exercise 7: Metaprogramming -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: A Term Exploder

In this question, we develop a string format for the `expr` metatype. By
default, there is no `has_repr` instance to print a nice string. For example: -/

#eval (expr.app (expr.var 0) (expr.var 1) : expr)   -- result: `[external]`
#eval (`(λx : ℕ, x + x) : expr)                     -- result: `[external]`

/-! 1.1. Define a metafunction `expr.repr` that converts an `expr` into a
`string`. It is acceptable to leave out some fields from the `expr`
constructors, such as the level `l` of a sort, the binder information `bi` of
a `λ` or `∀` binder, and the arguments of the `macro` constructor.

Hint: Use `name.to_string` to convert a name to a string, and `repr` for other
types that belong to the `has_repr` type class. -/

meta def expr.repr : expr → string
| (expr.var n)                := "(var " ++ repr n ++ ")"

/-! We register `expr.repr` in the `has_repr` type class, so that we can use
`repr` without qualification in the future, and so that it is available to
`#eval`. We need the `meta` keyword in front of the command we enter. -/

meta instance expr.has_repr : has_repr expr :=
{ repr := expr.repr }

/-! 1.2. Test your setup. -/

#eval (expr.app (expr.var 0) (expr.var 1) : expr)
#eval (`(λx : ℕ, x + x) : expr)


/-! ## Question 2: `destruct_and` on Steroids

Recall from the lecture that `destruct_and` fails on easy goals such as -/

lemma abc_ac₂ (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ c :=
sorry

/-! We will now address this by developing a new tactic called `destro_and`,
which applies both **des**truction and in**tro**duction rules for conjunction.
It will also go automatically through the hypotheses instead of taking an
argument. We will develop it in three steps.

2.1. Develop a tactic `intro_ands` that replaces all goals of the form
`a ∧ b` with two new goals `a` and `b` systematically, until all top-level
conjunctions are gone.

For this, we can use tactics such as `tactic.repeat` (which repeatedly applies a
tactic on all goals and subgoals until the tactic fails on each of the goal) and
`tactic.applyc` (which can be used to apply a rule, in connection with backtick
quoting). -/

#check tactic.repeat
#check tactic.applyc

meta def intro_ands : tactic unit :=
tactic.repeat (tactic.applyc `and.intro)

lemma abcd_bd (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ d :=
begin
  intro_ands,
  /- The proof state should be as follows:

  2 goals
  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ b

  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ d -/
  repeat { sorry }
end

lemma abcd_bacb (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
begin
  intro_ands,
  /- The proof state should be as follows:

  4 goals
  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ b

  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ a

  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ c

  a b c d : Prop,
  h : a ∧ (b ∧ c) ∧ d
  ⊢ b -/
  repeat { sorry }
end

/-! 2.2. Develop a tactic `destruct_ands` that replaces hypotheses of the form
`h : a ∧ b` by two new hypotheses `h_left : a` and `h_right : b` systematically,
until all top-level conjunctions are gone.

Here is some pseudocode that you can follow:

1. Retrieve the list of hypotheses from the context. This is provided by the
   metaconstant `tactic.local_context`.

2. Find the first hypothesis (= term) with a type (= proposition) of the form
   `_ ∧ _`. Here, you can use the `list.mfirst` function, in conjunction with
   pattern matching. You can use `tactic.infer_type` to query the type of a
   term.

3. Perform a case split on the first found hypothesis. This can be achieved
   using `tactic.cases`, a metaprogram that corresponds roughly to `cases'`.

4. Repeat.

The above procedure might fail if there exists no hypotheses of the required
form. Make sure to handle this failure gracefully, for example using
`tactic.try` or `<|> pure ()`. -/

meta def destruct_ands : tactic unit :=
tactic.repeat (do 
  hs ← tactic.local_context,
  h ← list.mfirst (λh, do `(_ ∧ _) ← tactic.infer_type h, pure h) hs,
  tactic.cases h,
  pure ())

lemma abcd_bd₂ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ d :=
begin
  destruct_ands,
  /- The proof state should be as follows:

  a b c d : Prop,
  h_left : a,
  h_right_right : d,
  h_right_left_left : b,
  h_right_left_right : c
  ⊢ b ∧ d -/
  sorry
end

/-! 2.3. Combine the two tactics developed above and `tactic.assumption` to
implement the desired `destro_and` tactic. -/

meta def destro_and : tactic unit :=
do 
  destruct_ands,
  intro_ands,
  tactic.all_goals (tactic.try tactic.assumption),
  pure ()

lemma abcd_bd₃ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ d :=
by destro_and

lemma abcd_bacb₂ (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
by destro_and

lemma abd_bacb (a b c d : Prop) (h : a ∧ b ∧ d) :
  b ∧ (a ∧ (c ∧ b)) :=
begin
  destro_and,
  /- The proof state should be roughly as follows:

  a b c d : Prop,
  h_left : a,
  h_right_left : b,
  h_right_right : d
  ⊢ c -/
  sorry   -- unprovable
end

/-! 2.4. Provide some more examples for `destro_and` to convince yourself that
it works as expected also on more complicated examples. -/

-- enter your examples here


/-! ## Question 3 (**optional**): A Theorem Finder

We will implement a function that allows us to find theorems by constants
appearing in their statements. So given a list of constant names, the function
will list all theorems in which all these constants appear.

You can use the following metaconstants:

* `declaration` contains all data (name, type, value) associated with a
  declaration understood broadly (e.g., axiom, lemma, constant, etc.).

* `tactic.get_env` gives us access to the `environment`, a metatype that lists
  all `declaration`s (including all theorems).

* `environment.fold` allows us to walk through the environment and collect data.

* `expr.fold` allows us to walk through an expression and collect data.

3.1 (**optional**). Write a metafunction that checks whether an expression
contains a specific constant.

You can use `expr.fold` to walk through the expression, `||` and `ff` for
Booleans, and `expr.is_constant_of` to check whether an expression is a
constant. -/

meta def term_contains (e : expr) (nam : name) : bool :=
sorry

/-! 3.2 (**optional**). Write a metafunction that checks whether an expression
contains **all** constants in a list.

You can use `list.band` (Boolean and). -/

meta def term_contains_all (nams : list name) (e : expr) : bool :=
sorry

/-! 3.3 (**optional**). Produce the list of all theorems that contain all
constants `nams` in their statement.

`environment.fold` allows you to walk over the list of declarations. With
`declaration.type`, you get the type of a theorem, and with
`declaration.to_name` you get the name. -/

meta def list_constants (nams : list name) (e : environment) : list name :=
sorry

/-! Finally, we develop a tactic that uses the above metafunctions to log all
found theorems: -/

meta def find_constants (nams : list name) : tactic unit :=
do
  env ← tactic.get_env,
  list.mmap' tactic.trace (list_constants nams env)

/-! We test the solution. -/

run_cmd find_constants []   -- lists all theorems
run_cmd find_constants [`list.map, `function.comp]

end LoVe
