(* We can import a library about sets ("ensembles" in French). *)
Require Import Ensembles.
Require Import List. (* To deal with lists. *)
Export ListNotations.
Require Import Lia. (* Decision procedure for linear integer arithmetic *)


Section formulas.

(* First, let us define propositional formulas. *)

Inductive form : Type :=
 | Var : nat -> form
 | Bot : form
 | And : form -> form -> form
 | Or : form -> form -> form
 | Imp : form -> form -> form.

(* We define negation and top. *)

Definition Neg (A : form) := Imp A (Bot).
Definition fTop := Imp Bot Bot.

End formulas.

(* We use the following notations for formulas. *)

Notation "# p" := (Var p) (at level 1).
Notation "¬ φ" := (Imp φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := fTop.
Notation " φ ∧ ψ" := (And φ ψ) (at level 80, ψ at level 80).
Notation " φ ∨ ψ" := (Or φ ψ) (at level 85, ψ at level 85).
Notation " φ → ψ" := (Imp φ ψ) (at level 99, ψ at level 200).


Section more_notions.

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

Fixpoint weight  (φ : form) : nat := match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 2 + weight φ + weight ψ
| φ ∨ ψ => 1 + weight φ + weight ψ
| φ → ψ => 1 + weight φ + weight ψ
end.

End more_notions.



Section subformulas.

(* Next, we define the list of subformulas of a formula. *)

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

End subformulas.
