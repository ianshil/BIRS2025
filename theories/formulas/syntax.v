(* We can import a library about sets ("ensembles" in French). *)
Require Import Ensembles.
Require Import List. (* To deal with lists. *)
Export ListNotations.
Require Import Lia. (* Decision procedure for linear integer arithmetic *)


Section formulas.

(* First, let us define propositional formulas. *)

(* We define formulas inductively as an Inductive
   Type called "form". *)

Inductive form : Type :=
(* We give the constructors of this inductive type
   independently (constructors are separated by | ). *)
 | Var : nat -> form (* for propositional variables we have the constructor Var, 
                        which takes a natural number (nat) and outputs a formula. *)
 | Bot : form  (* We also have a constant bottom *)
 | And : form -> form -> form (* And takes two formulas and outputs a formula *)
 | Or : form -> form -> form (* Or does the same *)
 | Imp : form -> form -> form. (* Imp as well *)

(* For example, Var 2 is a formula. *)
Check Var 2.
(* So is the following *)
Check Imp (And (Var 2) (Var 3)) (Or Bot (Var 4)).
(* But the prefix notation is confusing... We will
   sort this out soon enough. *)


(* We define negation and top. *)
Definition Neg (A : form) := Imp A (Bot).
Definition fTop := Imp Bot Bot.
(* Calling it fTop to avoid clash with another library,
   but this won't matter for long. *)

End formulas.


(* We can get rid of the infix notation and use familiar
   latex symbols. This makes formulas much easier to read.. *)
Notation "# p" := (Var p) (at level 1).
Notation "¬ φ" := (Imp φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := fTop.
Notation " φ ∧ ψ" := (And φ ψ) (at level 80, ψ at level 80).
Notation " φ ∨ ψ" := (Or φ ψ) (at level 85, ψ at level 85).
Notation " φ → ψ" := (Imp φ ψ) (at level 99, ψ at level 200).

(* Let's check the two formulas again. *)
Check # 2.
(* So is the following *)
Check ((# 2) ∧ (# 3)) → (⊥ ∨ (# 4)).


Section more_notions.

(* We define the notion of uniform substitution.
   The function σ is a substitution over propositional
   variables (σ is of type nat -> form, but remember
   that our propositional variables are just nats!),
   and we define recursively on the structure of the
   formula φ how to apply the substitution σ to φ. *)

(* Fixpoint tells you that you are doing a recursive
   definition, so there must be either an inductive
   type (here form) or some other elements decreasing
   along a well-founded order, ensuring that the recursion
   is legitimate. *)
Fixpoint subst (σ : nat -> form) (φ : form) : form :=
(* We define the function on the structure of φ:
   this is what "match φ with ... end" does.
   We then need to inspect all patterns φ can have. *)
match φ with
| # p => (σ p) (* If it is a propositional variable, just apply σ to it! *)
| ⊥ => ⊥ (* If ⊥ leave the formula as it is *)
(* And for all other cases do a recursive call on the
   subformulas. *)
| ψ ∧ χ => (subst σ ψ) ∧ (subst σ χ)
| ψ ∨ χ => (subst σ ψ) ∨ (subst σ χ)
| ψ → χ => (subst σ ψ) → (subst σ χ)
end.

(* Let's see what we can do with this. *)
Compute subst (* We want to compute the subst of a function and a formula *)
    (fun n => # (n + n)) (* This is our function *)
    ((# 2) ∧ (# 3)) → (⊥ ∨ (# 4)) (* And our formula we saw above. *).


(* We can also define the implication of a formula by a list.
   Note that this time the recursive definition works because
   we use the (polymorphic) inductive type list. *)
Fixpoint list_Imp (φ : form) (l : list form) : form :=
match l with
 | nil => φ
 | ψ :: t => ψ → (list_Imp φ t)
end.

(* We can then create such implications. *)
Compute list_Imp (# 8) [⊤ ; (⊥ ∧ ⊤) ; (# 42)].


(* Other operations on lists of formulas we can
   perform consist in turning them into the
   conjunction / disjunction of all their elements. *)

Fixpoint list_conj (l : list form) :=
match l with
 | [] => ⊤
 | φ :: l => φ ∧ (list_conj l)
end.

(* Reminder about lists:
  [] is the empty list
  [φ] is a singleton list
  [φ1 ; ... ; φn] is a list of n elements 
  φ :: l is a notation for cons 
  l ++ l' is a notation for append *)

Compute list_conj [⊤ ; (⊥ ∧ ⊤) ; (# 42)].
(* Note that we have a conjunction of four elements,
   while our list only had 3! This is because we need
   to treat the empty list as well, and output ⊤ for it.
   ⊤ is in fact the rightmost conjunct, as it is defined
   as ¬⊥ (Coq simplified it for us).
   Logically, this is all fine as ⊤ is the unit element
   of ∧. *)

Fixpoint list_disj (l : list form) :=
match l with
 | nil => Bot
 | h :: t => Or h (list_disj t)
end.

Compute list_disj [⊤ ; (⊥ ∧ ⊤) ; (# 42)].
(* A similar phenomenon appears here with ⊥,
   the unit element of ∨. *)


(* We can also recursively define a notion of
   weight of formulas. It may look a bit weird for
   the case of conjunction, if you have never seen
   the terminating sequent calculus for intuitionistic
   logic. We'll get back to this later. *)
Fixpoint weight  (φ : form) : nat :=
match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 2 + weight φ + weight ψ
| φ ∨ ψ => 1 + weight φ + weight ψ
| φ → ψ => 1 + weight φ + weight ψ
end.

Compute weight (list_disj [⊤ ; (⊥ ∧ ⊤) ; (# 42)]).
Compute weight (list_Imp (list_disj [⊤ ; (⊥ ∧ ⊤) ; (# 42)]) [⊤ ; (⊥ ∧ ⊤) ; (# 42)]).

End more_notions.



Section subformulas.

(* Next, we define the list of subformulas of a formula. *)
Fixpoint subformlist (φ : form) : list form :=
match φ with
| # p => [# p]
| ⊥ => [⊥]
| ψ ∧ χ => (ψ ∧ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ ∨ χ => (ψ ∨ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ → χ => (ψ → χ) :: (subformlist ψ) ++ (subformlist χ)
end.

(* We can prove some sort of transitivitiy of subformlist:
   If a formula χ is a subformula of φ, and
   φ is a subformula of ψ, then
   χ is a subformula of ψ. *)

Lemma subform_trans : forall ψ χ φ, In φ (subformlist ψ) ->
  In χ (subformlist φ) -> In χ (subformlist ψ).
Proof.
(* We prove our statement by induction on ψ:
   this is what "induction ψ" do. *)
induction ψ ; 
(* Note that we do not put a "." after this tactic,
   but a ";". The semantic of "tac1 ; tac2" is 
   "do tac1 in the current environment, and then do
    tac2 on all environments generated by the application
    of tac1".
   So, by using ";" we can save ourselves from applying a single
   tactic several times in the generated subgoals. *)

(* What we need to prove remains a universally quantified formula.
   As one would do on paper, we introduce the quantified
   variables. This is what "intros" does. We specify the name
   of each variable after it. *)
intros χ φ H H0 ;
(* "cbn" simplifies an expression, and we require it
   to be applied in a specific location, this is what "in" does,
   and this location is everywhere, this is what "*" indicates. *)
cbn in * ;
(* The hypothesis "H" is "In φ (subformlist ψ)", but remember
   that we are doing an induction on "ψ", so the structure of
   "ψ" is inspected. Therefore, the expression "subformlist ψ"
   will be simplified by "cbn" when the structure of "ψ" will
   be made visible. This expression always reduce to an expression
   of the form "δ :: l" for some list "l" (inspect "subformlist" closely),
   so "In φ (subformlist ψ)" is reduced to an expression of the form
   "In φ (δ :: l)", which is reduced to the disjunction "φ = δ \/ In φ l".
   We can therefore "destruct" this disjunction and make a case analysis.
   This is why we do "destruct H". *)
destruct H ; 
(* "subst" performs all the substitutions given by the equalities
   in our set of assumptions, and "auto" tries to prove automatically
   our goal (if it does not succeed it leaves the goal / assumptions
   as they are). *)
subst ; auto.
(* After doing the above we only have 3 cases left. We 
   separate them with "-", which allows us to focus on
   the first goal. *)
- (* How do we prove this goal? Well, "H" tells us that 
     φ is in the list of subformulas of "ψ1"
     appended by the list of subformulas of "ψ2".
     So, "φ" should really be in one of those two lists.
     How can we infer this? A good tool is "Search"
     (say hi to your new best friend), which spits out
     what Rocq know at that point about the notions you
     ask about. *)
  Search In "++".
  (* Note that we can search about notion in plain text, like "In",
     but also about notations, like "++". For the latter you just
     need to put quotation marks around the notation. *)

  (* We note that the 3rd element in the list is what we need:
     it transform the fact of being "In" an appended list
     into the fact of being in the first part or second part
     of the appended list. As what we get is a disjunction,
     we can destruct it. *)
  apply in_app_or in H ; destruct H.
  + right. (* To prove a disjunction, we need to pick a disjunct. *)
    apply in_or_app ; left. (* Then we apply the converse of in_app_or. *)
    (* We can apply the induction hypothesis "IHψ1". Note that we specify
       that we want to apply IHw with the variable "φ" (in "IHψ1")
       instantiated by "φ" (in our context). If we did not do that,
       Rocq would complain as it cannot guess which value of "φ" we
       want to use. 
       Then we finish our goal automatically. *)
    apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
- apply in_app_or in H ; destruct H.
  + right. apply in_or_app ; left. apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
- apply in_app_or in H ; destruct H.
  + right. apply in_or_app ; left. apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
(* And that's our first proof! Woohoo!
   We close it by writing "Qed."*)
Qed.

Lemma subform_weight φ ψ : In ψ (subformlist φ) -> weight ψ <= weight φ.
Proof.
Admitted.

End subformulas.
