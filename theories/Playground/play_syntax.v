(* First, let us define propositional formulas. *)

Inductive form : Type :=
 | Var : nat -> form
 | Bot : form
 | And : form -> form -> form
 | Or : form -> form -> form
 | Imp : form -> form -> form.

(* We define negation and top. *)

Definition Neg (A : form) := Imp A (Bot).
Definition Top := Imp Bot Bot.

(* We use the following notations for modal formulas. *)

Notation "# p" := (Var p) (at level 1).
Notation "¬ φ" := (Imp φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := Top.
Notation " φ ∧ ψ" := (And φ ψ) (at level 80, ψ at level 80).
Notation " φ ∨ ψ" := (Or φ ψ) (at level 85, ψ at level 85).
Notation " φ → ψ" := (Imp φ ψ) (at level 99, ψ at level 200).



(* We can import a library about sets ("ensembles" in French). *)

Require Import Ensembles.

(* Next, we define the set of subformulas of a formula, and
    extend this notion to lists of formulas. *)

Fixpoint subform (φ : form) : Ensemble form :=
match φ with
| Var p => Singleton _ (Var p)
| ⊥ => Singleton _ ⊥
| ψ ∧ χ => Union _ (Singleton _ (ψ ∧ χ)) (Union _ (subform ψ) (subform χ))
| ψ ∨ χ => Union _ (Singleton _ (ψ ∨ χ)) (Union _ (subform ψ) (subform χ))
| ψ → χ => Union _ (Singleton _ (ψ → χ)) (Union _ (subform ψ) (subform χ))
end.

Lemma subform_id : forall φ, (subform φ) φ.
Proof.
destruct φ ; cbn. 1-2: split. all: left ; split.
Qed.




(* We can also talk about the same notion but with lists. 
   So, let's import the library about lists. *)

Require Import List.
Export ListNotations. (* And notations for lists. *)

Fixpoint subformlist (φ : form) : list form :=
match φ with
| Var p => (Var p) :: nil
| ⊥ => [⊥]
| ψ ∧ χ => (ψ ∧ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ ∨ χ => (ψ ∨ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ → χ => (Imp ψ χ) :: (subformlist ψ) ++ (subformlist χ)
end.

(* We can prove some sort of transitivitiy of subformlist. *)

Lemma subform_trans : forall φ ψ χ, List.In φ (subformlist ψ) ->
  List.In χ (subformlist φ) -> List.In χ (subformlist ψ).
Proof.
intros φ ψ χ. revert ψ χ φ. induction ψ ; intros ; cbn in * ;
destruct H ; subst ; auto.
- apply in_app_or in H ; destruct H.
  + right. apply in_or_app ; left. apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
- apply in_app_or in H ; destruct H.
  + right. apply in_or_app ; left. apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
- apply in_app_or in H ; destruct H.
  + right. apply in_or_app ; left. apply IHψ1 with (φ:=φ) ; auto.
  + right. apply in_or_app ; right. apply IHψ2 with (φ:=φ) ; auto.
Qed.

(* Equality is decidable over formulas. *)

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
repeat decide equality.
Qed.

(* We define the notion of uniform substitution. *)

Fixpoint subst (σ : nat -> form) (φ : form) : form :=
match φ with
| # p => (σ p)
| ⊥ => ⊥
| ψ ∧ χ => (subst σ ψ) ∧ (subst σ χ)
| ψ ∨ χ => (subst σ ψ) ∨ (subst σ χ)
| ψ → χ => (subst σ ψ) → (subst σ χ)
end.

(* We can also define the implication of a formula by a list. *)

Fixpoint list_Imp (A : form) (l : list form) : form :=
match l with
 | nil => A
 | h :: t => h → (list_Imp A t)
end.

(* We can transform a list of formulas into the conjunction / disjunction
   of all its elements. *)

Fixpoint list_conj (l : list form) :=
match l with
 | [] => ⊤
 | φ :: l => φ ∧ (list_conj l)
end.

Fixpoint list_disj (l : list form) :=
match l with
 | nil => Bot
 | h :: t => Or h (list_disj t)
end.

Lemma In_form_dec : forall l (A : form), {List.In A l} + {List.In A l -> False}.
Proof.
induction l ; simpl ; intros ; auto.
destruct (IHl A) ; auto.
destruct (eq_dec_form a A) ; auto.
right. intro. destruct H ; auto.
Qed.



