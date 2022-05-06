/-
 These are my solutions to the Codewars katas in Lean (level 8kyu)
-/

import tactic
import data.nat.prime
import logic.function.basic

namespace kyu.multiply

 /-
  You are asked to figure out why this definition
  does not execute properly.

  -- def multiply (a, b ∈ ℕ) ∈ ℕ := a × b
 -/

 -- 01
 def multiply (a b : ℕ) := a * b

end kyu.multiply

namespace kyu.kata
 /-
  You are asked to prove the following
   ∀ (n : ℕ), 1 = 2 * n -> false
 -/

 -- 02
 lemma kata : ∀ (n : ℕ), 1 = 2 * n -> false :=
 begin
   refine forall_not_of_not_exists _,
   exact of_to_bool_ff rfl
 end
end kyu.kata

namespace kyu.not_not_not
 /-
  You are asked to prove that we have
   ¬¬¬P → ¬P
 -/

 -- 03
 theorem not_not_not 
   (P : Prop) :
   ¬ ¬ ¬ P → ¬ P := 
 begin
   intros h hy,
   apply h,
   intros ye,
   apply ye,
   assumption
 end
end kyu.not_not_not

namespace kyu.bad_theorem
 /-
  You are asked to disprove the following proposition,
  i.e., that symmetry implies transitivity which in turn implies reflexivity
 -/
 def bad_theorem : Prop := 
   ∀ (α : Type) (r : α → α → Prop), symmetric r → transitive r → reflexive r

 --04
 theorem correct_version : ¬ bad_theorem :=
 begin
   simp [bad_theorem],
   refine ⟨_,_,_,_,_⟩,
    { exact Prop },
    { exact empty_relation },
    all_goals { simp [symmetric,transitive,reflexive,empty_relation] }
 end
end kyu.bad_theorem

namespace kyu.fermat_was_wrong
 /-
  You are asked to disprove the following conjecture that Fermat made,
  i.e., that we have 2^2^n + 1 is always prime
 -/

 -- 05
 theorem fermat_was_wrong : ¬ (∀ n : ℕ, nat.prime (2^2^n + 1)) :=
 by { refine not_forall_of_exists_not _, use 5, norm_num }
end kyu.fermat_was_wrong


namespace kyu.hello_world
 /- 
  Here you are given some definitions and theorems on natural numbers and are asked to complete them
 -/

 -- this defines a natural number
 inductive mynat : Type
 | zero : mynat
 | succ : mynat → mynat

 open mynat

 -- this defines the number two
 def two : mynat := succ (succ zero)

 -- this defines the predecessor
 def pred : mynat → mynat :=
  λ n, mynat.cases_on n
    zero
    (λ n', n')

 -- this defines addition
 def add : mynat → mynat → mynat :=
  λ n m, mynat.rec_on m
    n
    (λ m' add_n_m', succ (add_n_m'))

 inductive myeq : Π {α : Type}, α → α → Prop
 | myrefl : ∀ {α : Type} {a : α}, myeq a a

 open myeq

 def this_is_free : myeq (succ zero) (succ zero) :=
  myrefl

 theorem this_is_almost_free :
  myeq (add two zero) (add zero two) :=
 begin
  apply myrefl
 end

 --06.1
 theorem cong : ∀ (f : mynat → mynat) (n m : mynat),
  myeq n m → myeq (f n) (f m) :=
 begin
  intros f n m hnm,
  cases hnm,
  exact myrefl
 end

 --06.2
 theorem add_n_zero : ∀ n : mynat, myeq (add n zero) n :=
 begin
   intro n,
  exact myrefl
 end

 --06.3
 theorem add_zero_n : ∀ n : mynat, myeq (add zero n) n :=
 begin

  intros n,
  induction n,
  case zero : {
    exact myrefl
  },
  case succ : n' ihn' {
    show myeq (succ (add zero n')) (succ n'),
    apply cong,
    exact ihn'
  }
 end

end kyu.hello_world

namespace kyu.inverse_function
 /-
  You are asked to prove that any inverse (left and right) of an involutive function is itself
 -/
 open function

 --07.1
 lemma left {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : left_inverse g f) : f = g :=
 by { ext, exact (eq.symm (hfg (f x))).trans (congr_arg g (hf x)) }

 --07.2
 lemma right {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : right_inverse g f) : f = g :=
 by { ext, exact (congr_arg f (eq.symm (hfg x))).trans (hf (g x)) }
end kyu.inverse_function
