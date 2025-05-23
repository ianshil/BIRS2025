(* We can import a library about sets ("ensembles" in French). *)
Require Import Ensembles.
From stdpp Require Import countable. (* To talk about countability. *)


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

Lemma weight_pos  φ : weight φ > 0.
Proof. induction φ; simpl; lia. Qed.

(** We obtain an induction principle based on weight. *)
Definition weight_ind  (P : form -> Type) :
 (forall ψ, (forall φ, (weight φ < weight ψ) -> P φ) -> P ψ) ->
 (forall φ, P φ).
Proof.
  intros Hc φ. remember (weight φ) as w.
  assert(Hw : weight φ ≤ w) by now subst. clear Heqw.
  revert φ Hw. induction w; intros φ Hw.
  - pose (Hw' := weight_pos φ). auto with *.
  - destruct φ; simpl in Hw; trivial;
    apply Hc; intros φ' Hw'; apply IHw; simpl in Hw'; lia.
Defined.

Definition form_order  φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order  : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order  : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).

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






(* The results below are mostly useful to have a calculus
   based on multisets (which requires the base type to be
   countable and have equality decidable on it). 
   These lines are mainly taken from a work by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Formulas.v *)


(* Theory of countability from Iris.
    Will be useful for showing that we can enumerate
    our formulas.  *)
From stdpp Require Import countable.
Require Import Coq.Program.Equality.

Global Instance fomula_bottom : base.Bottom form := Bot.
Global Instance fomula_top : base.Top form := fTop.

Section decidable_countable.

(* Equality is decidable over formulas. *)

Global Instance form_eq_dec : EqDecision form.
Proof.
intros x y. unfold Decision. repeat decide equality.
Defined.

(* Elementhood in a list of formulas is decidable. *)

Lemma In_form_dec : forall l (A : form), {List.In A l} + {List.In A l -> False}.
Proof.
induction l ; simpl ; intros ; auto.
destruct (IHl A) ; auto.
destruct (form_eq_dec a A) ; auto.
right. intro. destruct H ; auto.
Qed.

(** ** Countability of the set of formulas *)
(** We prove that there are countably many formulas by exhibiting an injection
  into general trees over nat for countability. *)
Local Fixpoint form_to_gen_tree  (φ : form) : gen_tree (option nat) :=
match φ with
| Bot => GenLeaf  None
| Var v => GenLeaf (Some v)
| φ ∧ ψ => GenNode 0 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ ∨ ψ => GenNode 1 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ →  ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
end.

Local Fixpoint gen_tree_to_form  (t : gen_tree (option nat)) : option form :=
match t with
| GenLeaf None => Some Bot
| GenLeaf (Some v) => Some (Var v)
| GenNode 0 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∧ ψ)
| GenNode 1 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∨ ψ)
| GenNode 2 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ →  ψ)
| _=> None
end.

Global Instance form_count : Countable form.
Proof.
  eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
  intro φ; induction φ; simpl; trivial; now rewrite IHφ1, IHφ2 || rewrite  IHφ.
Defined.

End decidable_countable.

