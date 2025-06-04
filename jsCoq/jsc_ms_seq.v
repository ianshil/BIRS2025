
(* PART 1 : SYNTAX *)


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





























(* PART 2 : SYNTAX FACTS *)

From stdpp Require Import countable. (* To talk about countability. *)

Section order.

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

End order.


(* The results below are mostly useful to have a calculus
   based on multisets (which requires the base type to be
   countable and have equality decidable on it). 
   
   These lines are mainly taken from a work by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Formulas.v *)


(* Theory of countability from Iris.
    Will be useful for showing that we can enumerate
    our formulas.  *)

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





























(* PART 3 : MULTISETS *)


(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Environments.v *)

(** * Environments

  An environment is a multiset of formulas. We rely on stdpp multisets
  mostly for their powerful multiset equivalence tactic. *)

(** Notion of wellfoundedness *)
Require Import Coq.Program.Wf.

(** Stdpp implementation of multisets *)
Require Import stdpp.gmultiset.

Require Import Coq.Program.Equality.

(** An environment is defined as a finite multiset of formulas
(in the sense of the stdpp library).
This requires decidable equality and countability of the underlying set. *)
Definition env := @gmultiset form form_eq_dec form_count.

Global Instance singleton  : Singleton form env := gmultiset_singleton.
Global Instance singletonMS  : SingletonMS form env := base.singleton.

Global Hint Unfold mult empty singleton union intersection env : mset.
(* useful notations :
  {[ x ]} : singleton
      ⊎ : disjoint union
   \: difference (setminus)
   {[ x; y; … ]} union of singletons
   [{[+ x; y; … +]}] *disjoint* union of singletons
      ⊂@ : include
*)

Definition empty  := ∅ : env.

Ltac ms :=
  unfold base.singletonMS, singletonMS, base.empty, gmultiset_empty in *;
  autounfold with mset in *; autounfold with mset;
  repeat rewrite gmultiset_elem_of_disj_union; try tauto;
  multiset_solver.

Notation "Γ • φ" := (disj_union Γ (base.singletonMS φ)) (at level 105, φ at level 85, left associativity).

Section GeneralEnvironments.

Global Instance proper_elem_of : Proper ((=) ==> (≡@{env}) ==> (fun x y => x <-> y)) elem_of.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Instance proper_disj_union : Proper ((≡@{env}) ==> (≡@{env}) ==> (≡@{env})) disj_union.
Proof. intros Γ Γ' Heq Δ Δ' Heq'. ms. Qed.

Lemma elements_env_add (Γ : env) φ : elements(Γ • φ) ≡ₚ φ :: elements Γ.
Proof.
setoid_rewrite (gmultiset_elements_disj_union Γ).
setoid_rewrite (gmultiset_elements_singleton φ).
symmetry. apply Permutation_cons_append.
Qed.

(** ** Multiset utilities *)

Lemma multeq_meq (M N: env) : (forall x, multiplicity x M = multiplicity x N) -> M ≡  N.
  Proof. multiset_solver. Qed.

Lemma diff_mult (M N : env) x:
  multiplicity x (M ∖ N) = (multiplicity x M - multiplicity x N)%nat.
Proof. apply multiplicity_difference. Qed.

Lemma union_mult (M N : env) x :
  multiplicity x (M ⊎ N) = (multiplicity x M + multiplicity x N)%nat.
Proof. apply multiplicity_disj_union. Qed.

Lemma singleton_mult_in x y: x = y -> multiplicity x {[+ y +]} = 1.
Proof.
  intro Heq. rewrite Heq. apply multiplicity_singleton. Qed.

Lemma singleton_mult_notin x y: x <> y -> multiplicity x {[y]} = 0.
Proof. apply multiplicity_singleton_ne. Qed.

(* Two useful basic facts about multisets containing (or not) certain elements. *)
Lemma env_replace {Γ : env} φ {ψ}:
  (ψ ∈ Γ) -> (Γ • φ) ∖ {[ψ]} ≡ (Γ ∖ {[ψ]} • φ).
Proof.
intro Hin. apply multeq_meq. intros θ.
rewrite diff_mult, union_mult, union_mult, diff_mult.
apply PeanoNat.Nat.add_sub_swap.
case (decide (θ = ψ)); intro; subst.
- now rewrite singleton_mult_in.
- rewrite singleton_mult_notin; trivial. lia.
Qed.

Lemma diff_not_in (Γ : env) φ : φ ∉ Γ -> Γ ∖ {[φ]} ≡ Γ.
Proof.
intro Hf. apply multeq_meq. intros ψ.
rewrite diff_mult. rewrite (elem_of_multiplicity φ Γ) in Hf.
unfold mult.
case (decide (φ = ψ)).
- intro; subst. lia.
- intro Hneq. setoid_rewrite (multiplicity_singleton_ne ψ φ); trivial. lia.
  auto.
Qed.

Lemma env_add_remove : ∀ (Γ: env) φ, (Γ • φ) ∖ {[φ]} = Γ.
Proof. intros; ms. Qed.

Local Definition in_subset {Γ : env} {Γ'} (Hi : Γ' ⊆ elements Γ) {ψ0} (Hin : ψ0 ∈ Γ') : ψ0 ∈ Γ.
Proof. apply gmultiset_elem_of_elements,Hi, Hin. Defined.

Lemma difference_singleton (Δ: env) φ: φ ∈ Δ -> Δ ≡ ((Δ ∖ {[φ]}) • φ).
Proof.
intro Hin. rewrite (gmultiset_disj_union_difference {[φ]}) at 1. ms.
now apply gmultiset_singleton_subseteq_l.
Qed.

Lemma env_in_add (Δ : env) ϕ φ: φ ∈ (Δ • ϕ) <-> φ = ϕ \/ φ ∈ Δ.
Proof.
rewrite (gmultiset_elem_of_disj_union Δ), gmultiset_elem_of_singleton.
tauto.
Qed.

Lemma equiv_disj_union_compat_r {Δ Δ' Δ'' : env} : Δ ≡ Δ'' -> Δ ⊎ Δ' ≡ Δ'' ⊎ Δ'.
Proof. ms. Qed.

Lemma env_add_comm (Δ : env) φ ϕ : (Δ • φ • ϕ) ≡ (Δ • ϕ • φ).
Proof. ms. Qed.

Lemma in_difference (Δ : env) φ ψ : φ ≠ ψ -> φ ∈ Δ -> φ ∈ Δ ∖ {[ψ]}.
Proof.
intros Hne Hin.
unfold elem_of, gmultiset_elem_of.
rewrite (multiplicity_difference Δ {[ψ]} φ).
assert( HH := multiplicity_singleton_ne φ ψ Hne).
unfold singletonMS, base.singletonMS in HH.
unfold base.singleton. ms.
Qed.

Hint Resolve in_difference : multiset.

(* could be used in disj_inv *)
Lemma env_add_inv (Γ Γ' : env) φ ψ:
  φ ≠ ψ ->
  ((Γ • φ) ≡ (Γ' • ψ)) ->
    (Γ' ≡  ((Γ ∖ {[ψ]}) • φ)).
Proof.
intros Hneq Heq. rewrite <- env_replace.
- ms.
- assert(ψ ∈ (Γ • φ)); [rewrite Heq|]; ms.
Qed.

Lemma env_add_inv' (Γ Γ' : env) φ: (Γ • φ) ≡ Γ' -> (Γ ≡  (Γ' ∖ {[φ]})).
Proof. intro Heq. ms. Qed.

Lemma env_equiv_eq (Γ Γ' :env) : Γ =  Γ' -> Γ ≡  Γ'.
Proof. intro; subst; trivial. Qed.

(* reprove the following principles, proved in stdpp for Prop, but
   we need them in Type *)
Lemma gmultiset_choose_or_empty (X : env) : {x | x ∈ X} + {X = ∅}.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - by apply gmultiset_elements_empty_inv.
  - exists x. rewrite <- (gmultiset_elem_of_elements x X).
    replace (elements X) with (x :: l). left.
Qed.

(* We need this induction principle in type. *)
Lemma gmultiset_rec (P : env → Type) :
  P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
Proof.
  intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
  destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' x X) by done.
  apply Hinsert, IH; multiset_solver.
Qed.

Lemma difference_include θ θ' (Δ : env) :
  (θ' ∈ Δ) ->
  θ ∈ Δ ∖ {[θ']} -> θ ∈ Δ.
Proof.
intros Hin' Hin.
rewrite gmultiset_disj_union_difference with (X := {[θ']}).
- apply gmultiset_elem_of_disj_union. tauto.
- now apply gmultiset_singleton_subseteq_l.
Qed.

Fixpoint rm x l := match l with
| h :: t => if form_eq_dec x h then t else h :: rm x t
| [] => []
end.

Lemma rm_comm l x y : rm x (rm y l) = rm y (rm x l).
Proof.
induction l ; cbn ; auto.
do 2 destruct form_eq_dec ; subst ; cbn ; auto.
- destruct form_eq_dec ; [auto | contradiction].
- destruct form_eq_dec ; [auto | contradiction].
- repeat destruct form_eq_dec ; subst ; auto ; try contradiction.
  rewrite IHl ; auto.
Qed.

Lemma in_rm l x y: In x (rm y l) -> In x l.
Proof.
induction l; simpl. tauto.
destruct form_eq_dec. tauto. firstorder.
Qed.

Lemma in_in_rm l x y: x ≠ y -> In x l -> In x (rm y l).
Proof.
intro H.
induction l; simpl ; auto. 
intro H0. destruct H0 ; subst ; destruct form_eq_dec ; subst ; try contradiction ; firstorder.
Qed.

Lemma remove_include θ θ' Δ : (θ' ∈ Δ) -> θ ∈ rm θ' Δ -> θ ∈ Δ.
Proof. intros Hin' Hin. eapply elem_of_list_In, in_rm, elem_of_list_In, Hin. Qed.

Lemma rm_notin l ψ : ψ ∉ l -> rm ψ l = l.
Proof.
induction l ; cbn ; auto.
intro. destruct (form_eq_dec ψ a) ; subst.
- exfalso. apply H ; left ; auto.
- f_equal. apply IHl. intro ; apply H ; right ; auto.
Qed. 


(* technical lemma : one can constructively find whether an environment contains
   an element satisfying a decidable property *)
Lemma decide_in (P : _ -> Prop) (Γ : env) :
  (forall φ, Decision (P φ)) ->
  {φ | (φ ∈ Γ) /\ P φ} + {forall φ, φ ∈ Γ -> ¬ P φ}.
Proof.
intro HP.
induction Γ using gmultiset_rec.
- right. intros φ Hφ; inversion Hφ.
- destruct IHΓ as [(φ&Hφ) | HF].
  + left. exists φ. ms.
  + case (HP x); intro Hx.
    * left; exists x. ms.
    * right. intros. ms.
Qed.

Lemma union_difference_L (Γ : env) Δ ϕ: ϕ ∈ Γ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ∖{[ϕ]} ⊎ Δ.
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Lemma union_difference_R (Γ : env) Δ ϕ: ϕ ∈ Δ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ⊎ (Δ ∖{[ϕ]}).
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Global Instance equiv_assoc : @Assoc env equiv disj_union.
Proof. intros x y z. ms. Qed.

Global Instance proper_difference : Proper ((≡@{env}) ==> eq ==> (≡@{env})) difference.
Proof. intros Γ Γ' Heq Δ Heq'. ms. Qed.

(** ** Tactics *)
(* helper tactic split cases given an assumption about belonging to a multiset *)

End GeneralEnvironments.

Global Ltac in_tac :=
repeat
match goal with
| H : ?θ  ∈ {[?θ1; ?θ2]} |- _ => apply gmultiset_elem_of_union in H; destruct H as [H|H]; try subst
| H : ?θ ∈ (?Δ ∖ {[?θ']}) |- _ => apply difference_include in H; trivial
| H : context [?θ  ∈ (?d • ?θ2)] |- _ =>
    rewrite (env_in_add d) in H; destruct H as [H|H]; try subst
| H : context [?θ ∈ {[ ?θ2 ]}] |- _ => rewrite gmultiset_elem_of_singleton in H; subst
end.


Global Hint Immediate equiv_assoc : proof.

Global Instance Proper_elements:
  Proper ((≡) ==> (≡ₚ)) ((λ Γ : env, gmultiset_elements Γ)).
Proof.
intros Γ Δ Heq ; apply AntiSymm_instance_0; apply gmultiset_elements_submseteq; ms.
Qed.

Lemma list_to_set_disj_env_add Δ v:
  ((list_to_set_disj Δ : env) • v : env) ≡ list_to_set_disj (v :: Δ).
Proof. ms. Qed.

Lemma list_to_set_disj_rm Δ v:
  (list_to_set_disj Δ : env) ∖ {[v]} ≡ list_to_set_disj (rm v Δ).
Proof.
induction Δ as [|φ Δ]; simpl; [ms|].
case form_eq_dec; intro; subst; [ms|].
simpl. rewrite <- IHΔ. case (decide (v ∈ (list_to_set_disj Δ: env))).
- intro. rewrite union_difference_R by assumption. ms.
- intro. rewrite diff_not_in by auto with *. rewrite diff_not_in; auto with *.
Qed.

Lemma gmultiset_elements_list_to_set_disj (l : list form):
  gmultiset_elements(list_to_set_disj l) ≡ₚ l.
Proof.
induction l as [| x l]; [ms|].
rewrite Proper_elements; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add; rewrite IHl. trivial.
Qed.

Lemma gmultiset_elements_list_to_set_disj_perm (l0 l1 : list form):
  l0 ≡ₚ l1 -> gmultiset_elements(list_to_set_disj l0) ≡ₚ l1.
Proof.
revert l1. induction l0 as [| x l]; [ms|]. intro.
rewrite Proper_elements ; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add ; rewrite IHl ; auto. trivial.
Qed.

Lemma rm_perm_inside l0 l1 ψ ϕ : rm ψ (ϕ :: l0 ++ l1) ≡ₚ rm ψ (l0 ++ ϕ :: l1).
Proof.
revert l1 ψ ϕ.
induction l0 ; intros ; cbn ; auto.
destruct (form_eq_dec ψ ϕ) ; subst.
- destruct (form_eq_dec ϕ a) ; subst ; auto.
  + apply Permutation_middle.
  + rewrite <- IHl0 ; cbn. destruct (form_eq_dec ϕ ϕ) ; subst ; try contradiction.
    auto.
- destruct (form_eq_dec ϕ a) ; subst ; auto.
  + destruct (form_eq_dec ψ a) ; try contradiction ; auto. rewrite <- IHl0 ; cbn.
    destruct (form_eq_dec ψ a) ; try contradiction ; auto.
  + destruct (form_eq_dec ψ a) ; try contradiction ; auto.
    * apply Permutation_middle.
    * rewrite <- IHl0 ; cbn. destruct (form_eq_dec ψ ϕ) ; subst ; try contradiction.
      apply perm_swap.
Qed.

Lemma rm_perm ψ : Proper ((≡ₚ@{form}) ==> (≡ₚ@{form})) (rm ψ).
Proof.
intros l0. induction l0.
- cbn ; intros. apply Permutation_nil_l in H ; subst ; auto.
- intros. symmetry in H. destruct (Permutation_vs_cons_inv H) as (y0 & y1 & Hy). subst.
  symmetry in H ; apply Permutation_cons_app_inv in H ; auto.
  pose (IHl0 _ H). rewrite <- rm_perm_inside.
  cbn ; destruct (form_eq_dec ψ a) ; subst ; auto.
Qed.

Lemma elements_setminus (Γ : env) ψ : elements (Γ ∖ {[ψ]}) ≡ₚ rm ψ (elements Γ).
Proof.
case (decide (ψ ∈ Γ)) ; intro H.
- apply difference_singleton in H.
  assert (elements Γ ≡ₚ elements (Γ ∖ {[ψ]} • ψ)) by (rewrite <- H ; auto).
  rewrite rm_perm ; [ | exact H0]. 
  rewrite rm_perm ; [ | apply elements_env_add].
  cbn. destruct (form_eq_dec ψ ψ) ; try contradiction ; auto.
- rewrite diff_not_in ; auto. rewrite rm_notin ; auto. intro.
  apply H. apply gmultiset_elem_of_elements ; auto.
Qed.
























(* PART 4 : MULTISET ORDERING *)

(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Order.v *)

(** * Ordering *)
Definition env_weight Γ :=
  list_sum (map (fun x => 5^ weight x) Γ).

Lemma env_weight_disj_union Γ Δ :
  env_weight (Γ ++ Δ) = env_weight Γ +  env_weight Δ.
Proof.
unfold env_weight. now rewrite map_app, list_sum_app.
Qed.

Notation "Δ '•' φ" := (cons φ Δ) : list_scope.

Lemma env_weight_add Γ φ :
  env_weight (Γ • φ) = env_weight Γ + (5 ^ weight φ).
Proof.
unfold env_weight. simpl. lia.
Qed.

Global Hint Rewrite env_weight_add : order.

Definition env_order := ltof _ env_weight.
Infix "≺" := env_order (at level 150).

Lemma env_weight_singleton (φ : form) :
  env_weight [ φ ] = 5 ^ weight φ.
Proof.
unfold env_weight, ltof. simpl. lia.
Qed.

Lemma env_order_singleton  φ ψ :
  weight φ < weight ψ -> [φ ] ≺ [ ψ ].
Proof.
intro Hw. unfold env_order, ltof. do 2 rewrite env_weight_singleton.
apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Definition env_order_refl Δ Δ' := (env_weight Δ) ≤(env_weight Δ').

Global Notation "Δ ≼ Δ'" := (env_order_refl Δ Δ') (at level 150).

Lemma env_order_env_order_refl Δ Δ' :
  env_order Δ Δ' -> env_order_refl Δ Δ'.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Lemma env_order_refl_trans Δ Δ' Δ'' :
  env_order_refl Δ Δ' -> env_order_refl Δ' Δ'' -> env_order_refl Δ Δ''.
Proof. unfold env_order_refl, ltof. lia. Qed.

Global Hint Resolve env_order_env_order_refl: order.

Lemma env_order_self Δ : Δ ≼ Δ.
Proof. unfold env_order_refl. trivial. Qed.

Global Instance Proper_env_weight : Proper ((≡ₚ) ==> (=)) env_weight.
Proof.
intros Γ Δ Heq. unfold env_weight. now rewrite Heq.
Qed.


Global Instance Proper_env_order_refl_env_weight:
  Proper ((env_order_refl) ==> le) env_weight.
Proof. intros Γ Δ Hle. auto with *. Qed.

Global Hint Resolve Proper_env_order_refl_env_weight : order.

Global Hint Unfold form_order : mset.


Global Instance env_order_trans : Transitive env_order.
Proof. unfold env_order, env_weight, ltof. auto with *. Qed.

Definition wf_env_order : well_founded env_order.
Proof. now apply well_founded_lt_compat with env_weight.
Defined.

(* We introduce a notion of "pointed" environment, which is simply
 * a pair (Δ, φ), where Δ is an environment and φ is a formula,
 * not necessarily an element of Δ.  *)
Definition pointed_env := (list (form) * form)%type.


(* The order on pointed environments is given by considering the
 * environment order on the sum of Δ and {φ}. *)
Definition pointed_env_order (pe1 : pointed_env) (pe2 : pointed_env) :=
  env_order (fst pe1 • snd pe1 • snd pe1) (fst pe2 • snd pe2 •  snd pe2).

Lemma wf_pointed_order : well_founded pointed_env_order.
Proof. apply well_founded_ltof. Qed.

Definition pointed_env_ms_order (Γφ Δψ : env * form) :=
  pointed_env_order (elements Γφ.1, Γφ.2) (elements Δψ.1, Δψ.2).

Lemma wf_pointed_env_ms_order: well_founded pointed_env_ms_order.
Proof. apply well_founded_ltof. Qed.

Infix "≺·" := pointed_env_order (at level 150).

Lemma env_order_equiv_right_compat {Δ Δ' Δ'' }:
  Δ' ≡ₚ Δ'' ->
  (Δ ≺ Δ'') ->
  Δ ≺ Δ'.
Proof.
unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial.
Qed.

Lemma env_order_equiv_left_compat {Δ Δ' Δ'' }:
  Δ ≡ₚ Δ'' ->
  (Δ'' ≺ Δ') ->
  Δ ≺ Δ'.
Proof. unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial. Qed.


Global Instance Proper_env_order:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order.
Proof.
  intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight.
  rewrite H12, H34. tauto.
Qed.

Global Instance Proper_env_order_refl:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order_refl.
Proof.
intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight, env_order_refl.
now rewrite H12, H34.
Qed.

Lemma env_order_1 Δ φ1 φ : weight φ1 < weight φ -> Δ • φ1 ≺ Δ • φ.
Proof.
intros Hw.  unfold env_order, ltof. do 2 rewrite env_weight_add.
apply Nat.add_lt_mono_l. apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Local Hint Resolve Nat.pow_lt_mono_r : order.

Lemma env_order_compat Δ Δ' φ1 φ :
  weight φ1 < weight φ -> (Δ' ≼ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_le_lt_mono; auto with *.
Qed.

Global Hint Resolve env_order_compat : order.

Lemma env_order_compat' Δ Δ' φ1 φ :
  weight φ1 ≤ weight φ -> (Δ' ≺ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_lt_le_mono; auto with *. now apply Nat.pow_le_mono_r.
Qed.

Global Hint Resolve env_order_compat' : order.

Lemma env_order_add_compat Δ Δ' φ : (Δ ≺ Δ') -> (Δ • φ) ≺ (Δ' • φ).
Proof.
unfold env_order, ltof. do 2 rewrite env_weight_add. lia.
Qed.

Lemma env_order_disj_union_compat_left Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ++ Δ' ≺ Δ'' ++ Δ'.
Proof.
unfold env_order, ltof. intro. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_right Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ' ++ Δ ≺ Δ' ++ Δ''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Global Hint Resolve env_order_disj_union_compat_right : order.

Lemma env_order_disj_union_compat Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_refl_disj_union_compat Δ Δ' Δ'' Δ''':
  (env_order_refl Δ Δ'') -> (env_order_refl Δ' Δ''') -> env_order_refl (Δ ++ Δ') (Δ'' ++ Δ''').
Proof.
unfold env_order_refl, env_order, ltof. repeat rewrite env_weight_disj_union.
intros Hle1 Hle2; try rewrite Heq1; try rewrite Heq2; try lia.
Qed.

Global Hint Resolve env_order_refl_disj_union_compat : order.

Hint Unfold env_order_refl : order.
Lemma env_order_disj_union_compat_strong_right Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≼ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros Hlt Hle. unfold env_order_refl, env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_strong_left Δ Δ' Δ'' Δ''':
  (Δ ≼ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros Hlt Hle. unfold env_order_refl, env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia. Qed.

Lemma env_order_0 Δ φ: Δ ≺ Δ • φ.
Proof.
unfold env_order, ltof. rewrite env_weight_add.
apply Nat.lt_add_pos_r. transitivity (5 ^ 0). simpl. lia. apply Nat.pow_lt_mono_r. lia.
apply weight_pos.
Qed.

Local Lemma pow5_gt_0 n : 1 ≤ 5 ^ n.
Proof. transitivity (5^0). simpl. lia. apply Nat.pow_le_mono_r; lia. Qed.

Local Hint Resolve pow5_gt_0: order.

Lemma env_order_0' Δ Δ' φ: (Δ' ≼ Δ) -> Δ' ≺ Δ • φ.
Proof.
intro H.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in H.
replace (weight φ) with (S (pred (weight φ))).
cbn. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
repeat (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia. destruct φ ; cbn ; lia.
Qed.

Lemma env_order_2 Δ Δ' φ1 φ2 φ: weight φ1 < weight φ -> weight φ2 < weight φ ->
  (Δ' ≼ Δ) -> Δ' • φ1 • φ2 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
repeat (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_3 Δ Δ' φ1 φ2 φ3 φ:
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> (Δ' ≼ Δ) ->
  Δ' • φ1 • φ2 • φ3 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 3 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_4 Δ Δ' φ1 φ2 φ3 φ4 φ:
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> weight φ4 < weight φ ->
   (Δ' ≼ Δ) -> Δ' • φ1 • φ2  • φ3 • φ4 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hw4 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 4 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_cancel_right Δ Δ' φ:  (Δ ≺ Δ') -> Δ ≺ (Δ' • φ).
Proof. etransitivity; [|apply env_order_0].	 assumption. Qed.

Lemma env_order_refl_add Δ Δ' φ: (Δ ≼ Δ') -> (Δ • φ) ≼ (Δ' • φ).
Proof. unfold env_order_refl. do 2 rewrite env_weight_add. lia. Qed.

Lemma env_order_refl_add' Δ Δ' φ φ': weight φ ≤ weight φ' -> (Δ ≼ Δ') -> (Δ • φ) ≼ (Δ' • φ').
Proof. unfold env_order_refl. do 2 rewrite env_weight_add.
intros. apply Nat.add_le_mono. lia. apply Nat.pow_le_mono_r; lia. Qed.

Global Hint Resolve env_order_0 : order.
Global Hint Resolve env_order_0' : order.
Global Hint Resolve env_order_1 : order.
Global Hint Resolve env_order_2 : order.
Global Hint Resolve env_order_3 : order.
Global Hint Resolve env_order_4 : order.
Global Hint Resolve env_order_add_compat : order.
Global Hint Resolve env_order_cancel_right : order.
Global Hint Resolve env_order_refl_add : order.
Global Hint Resolve env_order_refl_add' : order.
Global Hint Extern 1 (?a < ?b) => subst; simpl; lia : order.

Ltac get_diff_form g := match g with
| ?Γ ∖{[?φ]} => φ
| _ (?Γ ∖{[?φ]}) => φ
| _ (rm ?φ _) => φ
| (rm ?φ _) => φ
| ?Γ ++ _ => get_diff_form Γ
| _ :: ?Γ => get_diff_form Γ
end.

Ltac get_diff_env g := match g with
| ?Γ ∖{[?φ]} => Γ
| _ :: ?Γ => get_diff_env Γ
end.

Lemma remove_env_order Δ φ:  rm φ Δ ≼ Δ.
Proof.
unfold env_order_refl.
induction Δ as [|ψ Δ]. trivial.
simpl. destruct form_eq_dec; repeat rewrite env_weight_add; lia.
Qed.

Global Hint Resolve remove_env_order : order.

Lemma remove_In_env_order_refl Δ φ:  In φ Δ -> rm φ Δ • φ ≼ Δ.
Proof.
induction Δ as [|ψ Δ].
- intro Hf; contradict Hf.
- intros [Heq | Hin].
  + subst. simpl.  destruct form_eq_dec; [|tauto]. auto with order.
  + specialize (IHΔ Hin).  simpl. case form_eq_dec as [Heq | Hneq].
      * subst. auto with order.
      * rewrite (Permutation_swap ψ φ (rm φ Δ)). auto with order.
Qed.

Global Hint Resolve remove_In_env_order_refl : order.

Lemma env_order_lt_le_trans Γ Γ' Γ'' : (Γ ≺ Γ') -> (Γ' ≼ Γ'') -> Γ ≺ Γ''.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Lemma env_order_le_lt_trans Γ Γ' Γ'' : (Γ ≼ Γ') -> (Γ' ≺ Γ'') -> Γ ≺ Γ''.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Lemma remove_In_env_order Δ φ:  In φ Δ -> rm φ Δ ≺ Δ.
Proof.
intro Hin. apply remove_In_env_order_refl in Hin.
eapply env_order_lt_le_trans; [|apply Hin]. auto with order.
Qed.

Global Hint Resolve remove_In_env_order : order.

Lemma elem_of_list_In_1 {A : Type}: ∀ (l : list A) (x : A), x ∈ l <-> In x l.
Proof. apply elem_of_list_In. Qed.

Global Hint Resolve  elem_of_list_In_1 : order.

Lemma elements_elem_of {Γ : env} {φ : form} :
  φ ∈ Γ -> elements Γ ≡ₚ φ :: elements (Γ ∖ {[φ]}).
Proof.
  intro Hin. setoid_rewrite <- elements_env_add.
  apply Proper_elements, difference_singleton, Hin.
Qed.

Ltac prepare_order :=
repeat (apply env_order_add_compat);
unfold pointed_env_order; subst; simpl; try match goal with
| Δ := _ |- _ => subst Δ; try prepare_order
| Hin : ?a ∈ ?Γ |- context[elements ?Γ] => rewrite (elements_elem_of Hin); try prepare_order
| H : _ ∈ list_to_set_disj _ |- _ => apply elem_of_list_to_set_disj in H; try prepare_order
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (difference_singleton Γ ψ' H)) ||
    (eapply env_order_lt_le_trans ; [| apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial])
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ (?φ :: ?Γ)  => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ (_ :: _ :: ?Γ) => let ψ' := (get_diff_form Γ') in
apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))) ||
(eapply env_order_le_lt_trans; [| apply env_order_add_compat;
eapply env_order_lt_le_trans; [| (apply env_order_refl_add; apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial) ] ] )
|H : ?a = _ |- context[?a] => rewrite H; try prepare_order
end.

Lemma weight_Arrow_1 φ ψ : 1 < weight (φ → ψ).
Proof. simpl. pose (weight_pos  φ). lia. Qed.

Global Hint Resolve weight_Arrow_1 : order.

Ltac order_tac :=
try unfold pointed_env_ms_order; prepare_order;
repeat rewrite elements_env_add;
simpl; auto 10 with order;
try (apply env_order_disj_union_compat_right; order_tac).

Global Hint Extern 5 (?a ≺ ?b) => order_tac : proof.
Hint Extern 5 (?a ≺· ?b) => order_tac : proof.

Lemma pointed_env_order_bot_R pe Δ φ: (pe ≺· (Δ, ⊥)) -> pe ≺· (Δ, φ).
Proof.
intro Hlt. destruct pe as (Γ, ψ). unfold pointed_env_order. simpl.
eapply env_order_lt_le_trans. exact Hlt. simpl.
unfold env_order_refl. repeat rewrite env_weight_add.
assert(Hle: weight ⊥ ≤ weight φ) by (destruct φ; simpl; lia).
apply Nat.pow_le_mono_r with (a := 5) in Hle; lia.
Qed.

Hint Resolve pointed_env_order_bot_R : order.

Lemma pointed_env_order_bot_L pe Δ φ: ((Δ, φ) ≺· pe) -> (Δ, ⊥) ≺· pe.
Proof.
intro Hlt. destruct pe as (Γ, ψ). unfold pointed_env_order. simpl.
eapply env_order_le_lt_trans; [|exact Hlt]. simpl.
unfold env_order_refl. repeat rewrite env_weight_add.
assert(Hle: weight ⊥ ≤ weight φ) by (destruct φ; simpl; lia).
apply Nat.pow_le_mono_r with (a := 5) in Hle; lia.
Qed.

Hint Resolve pointed_env_order_bot_L : order.

Lemma weight_or_bot a b: weight(⊥) < weight (a ∨b).
Proof. destruct a; simpl; lia. Qed.

Hint Resolve weight_or_bot : order.

Definition pointed_env_order_refl pe1 pe2 :=
  env_order_refl (pe1.2 :: pe1.2 :: pe1.1) (pe2.2 :: pe2.2 :: pe2.1).





































  (* PART 5 : MULTISET-SEQUENT CALCULUS *)

(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Sequent.v *)

Open Scope stdpp_scope.

(** * Sequent calculus G4ip *)

(** We implement the sequent calculus G4ip, a contraction-free
 refinement of the usual Gentzen sequent calculus LJ for intuitionistic
 propositional logic, which was developed by the Soviet school of proof theory
 (Vorob'ev 1970) and introduced in the West by (Hudelmaier 1989) and (Dyckhoff
 1990). This calculus is also referred to as "LJT" in the literature, but we this
 name has also been used in the literature for other, unrelated calculi, so we 
 prefer to use "G4ip" to avoid ambiguity.

 The calculus G4ip is important because it allows for a terminating proof
 search, and in our proof of Pitts' theorem, it therefore lets us perform
 well-founded induction on proofs. Technically, this is thanks to the absence of
 a contraction rule. The left implication rule is refined into four separate
 proof rules.  *)

(** ** Definition of provability in G4ip *)
Reserved Notation "Γ ⊢ φ" (at level 90).
Inductive Provable : env -> form -> Type :=
| PId :  ∀ Γ p,      Γ • (Var p) ⊢ (Var p)
| BotL : ∀ Γ φ,      Γ • ⊥ ⊢ φ
| AndR : ∀ Γ φ ψ,
    Γ ⊢ φ ->
    Γ ⊢ ψ ->
      Γ ⊢ (φ ∧ ψ)
| AndL : ∀ Γ φ ψ θ,
    Γ • φ • ψ ⊢ θ ->
      Γ • (φ ∧ ψ) ⊢ θ
| OrR1 :    ∀ Γ φ ψ,
    Γ ⊢ φ ->
      Γ ⊢ (φ ∨ ψ)
| OrR2 :    ∀ Γ φ ψ,
    Γ ⊢ ψ ->
      Γ ⊢ (φ ∨ ψ)
| OrL :     ∀ Γ φ ψ θ,
    Γ • φ  ⊢ θ ->
    Γ • ψ ⊢ θ ->
      Γ • (φ ∨ ψ) ⊢ θ
| ImpR : ∀ Γ φ ψ,
    Γ • φ ⊢ ψ ->
      Γ ⊢ (φ → ψ)
| ImpLVar : ∀ Γ p φ ψ,
    Γ • Var p • φ ⊢ ψ ->
      Γ • Var p • (Var p → φ) ⊢ ψ
| ImpLAnd : ∀  Γ φ1 φ2 φ3 ψ,
    Γ • (φ1 → (φ2 → φ3)) ⊢ ψ ->
      Γ • ((φ1 ∧ φ2) → φ3) ⊢ ψ
| ImpLOr :  ∀  Γ φ1 φ2 φ3 ψ,
    Γ • (φ1 → φ3) • (φ2 → φ3) ⊢ ψ ->
      Γ • ((φ1 ∨ φ2) → φ3) ⊢ ψ
| ImpLImp : ∀  Γ φ1 φ2 φ3 ψ,
    Γ • (φ2 → φ3) ⊢ (φ1 → φ2) ->
    Γ • φ3 ⊢ ψ ->
      Γ • ((φ1 → φ2) → φ3) ⊢ ψ
where "Γ ⊢ φ" := (Provable Γ φ).

Notation "Γ ⊢G4ip φ" := (Provable Γ φ) (at level 90).

Global Hint Constructors Provable : proof.

(** We show that equivalent multisets prove the same things. *)
Global Instance proper_Provable  : Proper ((≡@{env}) ==> (=) ==> (=)) Provable.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Ltac equiv_tac :=
  repeat rewrite <- list_to_set_disj_rm;
  repeat rewrite <- list_to_set_disj_env_add;
  repeat (rewrite <- difference_singleton; trivial);
  try rewrite <- list_to_set_disj_rm;
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms.

(** We introduce a tactic "peapply" which allows for application of a G4ip rule
   even in case the environment needs to be reordered *)
Ltac peapply th :=
  (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|try ms].

(** ** Tactics *)

(** We introduce a few tactics that we will need to prove the admissibility of
  the weakening and exchange rules in the proof calculus. *)

(** The tactic "exch" swaps the nth pair of formulas of a sequent, counting from the right. *)

Ltac exch n := match n with
| O => match goal with |- ?a • ?b • ?c ⊢ _ =>
  rewrite (proper_Provable _ _ (env_add_comm a b c) _ _ eq_refl) end
| S O => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_add_comm _ _ _)) _ _ eq_refl)
| S (S O) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _))) _ _ eq_refl)
| S (S (S O)) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _)))) _ _ eq_refl)
end.
(** The tactic "exhibit" exhibits an element that is in the environment. *)
Ltac exhibit Hin n := match n with
| 0 => rewrite (proper_Provable _ _ (difference_singleton _ _ Hin) _ _ eq_refl)
| 1 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (difference_singleton _ _ Hin)) _ _ eq_refl)
| 2 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin))) _ _ eq_refl)
| 3 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin)))) _ _ eq_refl)
end.

(** The tactic "forward" tries to change a goal of the form :

((Γ•φ ∖ {[ψ]}•…) ⊢ …

into

((Γ ∖ {[ψ]}•…•φ) ⊢ … ,

by first proving that ψ ∈ Γ. *)

Ltac forward := match goal with
| |- (?Γ•?φ) ∖ {[?ψ]} ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (env_replace φ Hin) _ _ eq_refl)
| |- (?Γ•?φ) ∖ {[?ψ]}•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_replace φ Hin)) _ _ eq_refl);
  exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))) _ _ eq_refl);
  exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl);
  exch 2; exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl);
  exch 3; exch 2; exch 1; exch 0
end.

(** The tactic "backward" changes a goal of the form :

((Γ ∖ {[ψ]}•…•φ) ⊢ …

into

((Γ•φ ∖ {[ψ]}•…) ⊢ …,

by first proving that ψ ∈ Γ.

*)

Ltac backward := match goal with
| |- ?Γ ∖ {[?ψ]}•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof);
  rewrite (proper_Provable _ _ (symmetry(env_replace _ Hin)) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); try exch 0;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r (env_replace _ Hin))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2; exch 3;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))))) _ _ eq_refl)
end.

(** The tactic "rw" rewrites the environment equivalence Heq under the nth formula in the premise. *)
Ltac rw Heq n := match n with
| 0 => erewrite (proper_Provable _ _ Heq _ _ eq_refl)
| 1 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r Heq) _ _ eq_refl)
| 2 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq)) _ _ eq_refl)
| 3 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq))) _ _ eq_refl)
| 4 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq)))) _ _ eq_refl)
| 5 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq))))) _ _ eq_refl)
end.

























(* PART 6 : A PATH TO CONTRACTION *)


(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/SequentProps.v *)

(** * Admissible rules in G4ip sequent calculus

This file contains important properties of the sequent calculus G4ip, defined in
Sequents.v, namely the admissibility of various inversion rules, weakening and
contraction. We draw various consequences from this that are used extensively in
the proof of correctness of propositional quantifiers. The first part of this
file closely follows proof in the paper:

(Dyckhoff and Negri 2000). R. Dyckhoff and S. Negri, Admissibility of Structural
Rules for Contraction-Free Systems of Intuitionistic Logic, Journal of Symbolic
Logic (65):4.
*)

(** ** Weakening *)

Theorem weakening  φ' Γ φ : Γ ⊢ φ -> Γ•φ' ⊢ φ.
Proof with (auto with proof).
intro H. revert φ'.
induction H; intro φ'; auto with proof; try (exch 0; auto with proof).
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- constructor 8; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- constructor 12; exch 0...
Qed.

Global Hint Resolve weakening : proof.

Theorem generalised_weakeningL  (Γ Γ' : env) φ: Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ'. ms.
Qed.

Theorem generalised_weakeningR  (Γ Γ' : env) φ: Γ' ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ as [ | x Γ IHΓ] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ. ms.
Qed.

Global Hint Extern 5 (?a <= ?b) => simpl in *; lia : proof.

(** ** Inversion rules *)

(** We prove that the following rules are invertible: implication right, and
  left, or left, top left (i.e., the appliction of weakening for the formula
  top), the four implication left rules, the and right rule and the application of the or right rule with bottom. *)

Lemma ImpR_rev  Γ φ ψ :
  (Γ ⊢ (φ →  ψ))
    -> Γ • φ ⊢  ψ.
Proof with (auto with proof).
intro Hp. dependent induction Hp; auto with proof; try exch 0.
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- constructor 12; exch 0...
Qed.

Global Hint Resolve ImpR_rev : proof.

Theorem generalised_axiom  Γ φ : Γ • φ ⊢ φ.
Proof with (auto with proof).
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ φ Hle.
induction w; intros Γ φ Hle.
- destruct φ ; cbn in Hle ; lia.
- destruct φ; simpl in Hle...
  dependent destruction φ1.
  + constructor 8. exch 0...
  + auto with proof.
  + apply ImpR, AndL. exch 1; exch 0. apply ImpLAnd.
    exch 0. apply ImpR_rev. exch 0...
  + apply ImpR. exch 0. apply ImpLOr.
    exch 1; exch 0...
  + apply ImpR. exch 0...
Qed.

Global Hint Resolve generalised_axiom : proof.

Local Ltac lazy_apply th:=
(erewrite proper_Provable;  [| |reflexivity]);  [eapply th|].

Local Hint Resolve env_in_add : proof.

Lemma AndL_rev  Γ φ ψ θ: (Γ•φ ∧ ψ) ⊢ θ  → (Γ•φ•ψ) ⊢ θ.
Proof.
intro Hp.
remember (Γ•φ ∧ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∧ ψ ]}) by ms.
assert(Hin : (φ ∧ ψ) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq. revert φ ψ Hin.
(* we massaged the goal so that the environment of the derivation on which we do
   the induction is not composite anymore *)
induction Hp; intros φ0 ψ0 Hin.
(* auto takes care of the right rules easily *)
- forward. auto with proof.
- forward. auto with proof.
- apply AndR; auto with proof.
(* the main case *)
- case(decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 4. exch 0. backward. backward. apply IHHp. ms.
(* only left rules remain. Now it's all a matter of putting the right principal
   formula at the front, apply the rule; and put back the front formula at the back
   before applying the induction hypothesis *)
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward. constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- forward. forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 10. backward. apply IHHp. ms.
- forward. constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 12; backward.
  + apply IHHp1. ms.
  + apply IHHp2. ms.
Qed.

Lemma OrL_rev  Γ φ ψ θ: (Γ•φ ∨ ψ) ⊢ θ  → (Γ•φ ⊢ θ) * (Γ•ψ ⊢ θ).
Proof.
intro Hp.
remember (Γ•φ ∨ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∨ ψ ]}) by ms.
assert(Hin : (φ ∨ ψ) ∈ Γ')by ms.
assert(Heq' : ((Γ' ∖ {[φ ∨ ψ]}•φ) ⊢ θ) * ((Γ' ∖ {[φ ∨ ψ]}•ψ) ⊢ θ));
[| split; rw Heq 1; tauto].
clear Γ HH Heq.
induction Hp.
- split; forward; auto with proof.
- split; forward; auto with proof.
- split; constructor 3; now (apply IHHp1 || apply IHHp2).
- split; forward; constructor 4; exch 0; do 2 backward; apply IHHp; ms.
- split; constructor 5; now apply IHHp.
- split; apply OrR2; now apply IHHp.
- case (decide ((φ0 ∨ ψ0) = (φ ∨ ψ))); intro Heq0.
  + dependent destruction Heq0; subst. split; [peapply Hp1| peapply Hp2].
  + split; forward; constructor 7; backward; (apply IHHp1||apply IHHp2); ms.
- split; constructor 8; backward; apply IHHp; ms.
- split; do 2 forward; exch 0; constructor 9; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 10; backward; apply IHHp; ms.
- split; forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.  
Qed.

Lemma TopL_rev  Γ φ θ: Γ•(⊥ → φ) ⊢ θ -> Γ ⊢ θ.
Proof.
remember (Γ•(⊥ → φ)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ⊥ → φ ]}) by ms.
assert(Hin : (⊥ → φ) ∈ Γ')by ms. clear HH.
intro Hp. rw Heq 0. clear Γ Heq. induction Hp;
try forward ; auto with proof.
- constructor 4. exch 0. do 2 backward. apply IHHp.  ms.
- constructor 7; backward; [apply IHHp1 | apply IHHp2];  ms.
- constructor 8. backward. apply IHHp. ms.
- forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- constructor 10. backward. apply IHHp. ms.
- constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- constructor 12; backward;  [apply IHHp1 | apply IHHp2]; ms.
Qed.

Local Hint Immediate TopL_rev : proof.

Lemma ImpLVar_rev  Γ p φ ψ: (Γ• # p•(# p → φ)) ⊢ ψ  → (Γ• # p •φ) ⊢ ψ.
Proof.
intro Hp.
remember (Γ• #p•(#p → φ)) as Γ' eqn:HH.
assert (Heq: (Γ•Var p) ≡ Γ' ∖ {[Var p → φ]}) by ms.
assert(Hin : (#p → φ) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0. do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; apply IHHp1 || apply IHHp2; ms.
- apply ImpR. backward. apply IHHp. ms.
- case (decide ((Var p0 → φ0) = (Var p → φ))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + do 2 forward. exch 0. apply ImpLVar. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
Qed.

(* inversion for ImpLImp is only partial *)
Lemma ImpLImp_prev  Γ φ1 φ2 φ3 ψ: (Γ•((φ1 → φ2) → φ3)) ⊢ ψ -> (Γ•φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 → φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 → φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 → φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp2.
  + forward. apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
Qed.

Lemma ImpLOr_rev  Γ φ1 φ2 φ3 ψ:
  Γ•((φ1 ∨ φ2) → φ3) ⊢ ψ -> Γ•(φ1 → φ3)•(φ2 → φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 ∨ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∨ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∨ φ2) → φ3) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward; constructor 10. backward. apply IHHp. ms.
- case (decide (((φ0 ∨ φ4) → φ5) = ((φ1 ∨ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.
Qed.

Lemma ImpLAnd_rev  Γ φ1 φ2 φ3 ψ: (Γ•(φ1 ∧ φ2 → φ3)) ⊢ ψ ->  (Γ•(φ1 → φ2 → φ3)) ⊢ ψ .
Proof.
intro Hp.
remember (Γ •((φ1 ∧ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∧ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∧ φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 ∧ φ4) → φ5) = ((φ1 ∧ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 10. backward. apply IHHp. ms.
- forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.
Qed.

Global Hint Resolve AndL_rev : proof.
Global Hint Resolve OrL_rev : proof.
Global Hint Resolve ImpLVar_rev : proof.
Global Hint Resolve ImpLOr_rev : proof.
Global Hint Resolve ImpLAnd_rev : proof.


Lemma exfalso  Γ φ: Γ ⊢ ⊥ -> Γ ⊢ φ.
Proof.
intro Hp. dependent induction Hp; try tauto; auto with proof; tauto.
Qed.

Global Hint Immediate exfalso : proof.

Lemma AndR_rev  {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ1) * (Γ ⊢ φ2).
Proof.
  intro Hp. dependent induction Hp generalizing φ1 φ2 Hp ;
  try specialize (IHHp _ _ eq_refl) ;
  try specialize (IHHp1 _ _ eq_refl);
  try specialize (IHHp2 _ _ eq_refl);
  intuition;
  auto with proof.
Qed.


(** A general inversion rule for disjunction is not admissible. However, inversion holds if one of the formulas is ⊥. *)

Lemma OrR1Bot_rev  Γ φ :  Γ ⊢ φ ∨ ⊥ -> Γ ⊢ φ.
Proof. intro Hd.
 dependent induction Hd generalizing φ; auto using exfalso with proof. Qed.

Lemma OrR2Bot_rev  Γ φ :  Γ ⊢ ⊥ ∨ φ -> Γ ⊢ φ.
Proof. intro Hd. dependent induction Hd; auto using exfalso with proof. Qed.


(** We prove Lemma 4.1 of (Dyckhoff & Negri 2000). This lemma shows that a
    weaker version of the ImpL rule of Gentzen's original calculus LJ is still
    admissible in G4ip. The proof is simple, but requires the inversion lemmas
    proved above.
  *)

Lemma weak_ImpL  Γ φ ψ θ :Γ ⊢ φ -> Γ•ψ ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof with (auto with proof).
intro Hp. revert ψ θ. induction Hp; intros ψ0 θ0 Hp'.
- apply ImpLVar, Hp'.
- auto with proof.
- auto with proof.
- exch 0; constructor 4; exch 1; exch 0...
- auto with proof.
- apply ImpLOr. exch 0...
- exch 0; constructor 7; exch 0.
  + apply IHHp1. exch 0. eapply fst, OrL_rev. exch 0. exact Hp'.
  + apply IHHp2. exch 0. eapply snd, OrL_rev. exch 0. exact Hp'.
- auto with proof.
- exch 0; exch 1. constructor 9. exch 1; exch 0...
- exch 0. apply ImpLAnd. exch 0...
- exch 0. apply ImpLOr. exch 1; exch 0...
- exch 0. apply ImpLImp; exch 0. auto with proof. apply IHHp2. exch 0.
  eapply ImpLImp_prev. exch 0. eassumption.
Qed.

Global Hint Resolve weak_ImpL : proof.

(** ** Contraction

 The aim of this section is to prove that the contraction rule is admissible in
 G4ip. *)

(** An auxiliary definition of **height** of a proof, measured along the leftmost branch. *)
Fixpoint height  {Γ φ} (Hp : Γ ⊢ φ) := match Hp with
| PId _ _ => 1
| BotL _ _ => 1
| AndR Γ φ ψ H1 H2 => 1 + height H1 + height H2
| AndL Γ φ ψ θ H => 1 + height H
| OrR1 Γ φ ψ H => 1 + height H
| OrR2 Γ φ ψ H => 1 + height H
| OrL Γ φ ψ θ H1 H2 => 1 + height H1 + height H2
| ImpR Γ φ ψ H => 1 + height H
| ImpLVar Γ p φ ψ H => 1 + height H
| ImpLAnd Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLOr Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLImp Γ φ1 φ2 φ3 ψ H1 H2 => 1 + height H1 + height H2
end.

Lemma height_0  {Γ φ} (Hp : Γ ⊢ φ) : height Hp <> 0.
Proof. destruct Hp; simpl; lia. Qed.

(** Lemma 4.2 in (Dyckhoff & Negri 2000), showing that a "duplication" in the context of the implication-case of the implication-left rule is admissible. *)

Lemma ImpLImp_dup  Γ φ1 φ2 φ3 θ:
  Γ•((φ1 → φ2) → φ3) ⊢ θ ->
    Γ•φ1 •(φ2 → φ3) •(φ2 → φ3) ⊢ θ.
Proof.
intro Hp.
remember (Γ•((φ1 → φ2) → φ3)) as Γ0 eqn:Heq0.
assert(HeqΓ : Γ ≡ Γ0 ∖ {[((φ1 → φ2) → φ3)]}) by ms.
rw HeqΓ 3.
assert(Hin : ((φ1 → φ2) → φ3) ∈ Γ0) by (subst Γ0; ms).
clear Γ HeqΓ Heq0.
(* by induction on the height of the derivation *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ0 θ Hp Hleh Hin. induction h as [|h]; intros Γ θ Hp Hleh Hin;
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh.
- forward. auto with proof.
- forward. auto with proof.
- apply AndR.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- forward. apply AndL. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- apply OrR1. apply IHh with Hp. lia. ms.
- apply OrR2. apply IHh with Hp. lia. ms.
- forward. apply OrL; backward.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- apply ImpR. backward. apply IHh with Hp. lia. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward.
  apply IHh with Hp. lia. ms.
- forward. apply ImpLAnd. backward. apply IHh with Hp. lia. ms.
- forward. apply ImpLOr. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq.
  + dependent destruction Heq; subst.
    apply weak_ImpL.
    * exch 0. apply ImpR_rev. peapply Hp1.
    * do 2 (exch 0; apply weakening). peapply Hp2.
  + forward. apply ImpLImp; backward.
    * apply IHh with Hp1. lia. ms.
    * apply IHh with Hp2. lia. ms.
Qed.

(* technical lemma for contraction *)
Local Lemma p_contr  Γ φ θ:
  (Γ•φ•φ) ∖ {[φ]} ⊢ θ ->
  ((Γ•φ) ⊢ θ).
Proof. intros * Hd; peapply Hd. Qed.


(** Admissibility of contraction in G4ip. *)
Lemma contraction  Γ ψ θ : Γ • ψ • ψ ⊢ θ -> Γ • ψ ⊢ θ.
Proof.
remember (Γ•ψ•ψ) as Γ0 eqn:Heq0.
assert(HeqΓ : (Γ•ψ) ≡ Γ0 ∖ {[ψ]}) by ms.
intro Hp. rw HeqΓ 0.
assert(Hin : ψ ∈ Γ0) by (subst Γ0; ms).
assert(Hin' : ψ ∈ Γ0 ∖ {[ψ]}) by(rewrite <- HeqΓ; ms).
clear Γ HeqΓ Heq0. revert Hp.
(* by induction on the weight of ψ *)
remember (weight ψ) as w.
assert(Hle : weight ψ ≤ w) by lia.
clear Heqw. revert Γ0 ψ θ Hle Hin Hin'.
induction w; intros Γ ψ θ Hle Hin Hin' Hp; [destruct ψ; simpl in Hle; lia|].
(* by induction on the height of the premise *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ θ Hp Hleh Hin Hin'. revert ψ Hle; induction h as [|h]; intros ψ Hle Γ θ Hp Hleh Hin Hin';
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh, Hle.
- case(decide (ψ = Var p)).
  + intro; subst. exhibit Hin' 0. apply PId.
  + intro Hneq. forward. apply PId.
- case(decide (ψ = ⊥)).
  + intro; subst. exhibit Hin' 0. apply BotL.
  + intro. forward. apply BotL.
- apply AndR.
  + apply (IHh ψ Hle) with Hp1. lia. ms. ms.
  + apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- case (decide (ψ = (φ ∧ ψ0))); intro Heq.
  + subst. exhibit Hin' 0. apply AndL.
    apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply p_contr. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply AndL_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- (difference_singleton _ _ Hin'). ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply AndL. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR1. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR2. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ ∨ ψ0))); intro Heq.
  + subst. exhibit Hin' 0.
    apply OrL.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (fst (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp1.
      rewrite <- env_replace; ms.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (snd (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp2.
      rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply OrL; backward.
    * apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- apply ImpR. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (#p → φ))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    assert(Hcut : (((Γ•Var p) ∖ {[Var p → φ]}•(Var p → φ)) ⊢ ψ0)); [|peapply Hcut].
    forward. exch 0. apply ImpLVar, p_contr.
    apply IHw. simpl in Hle; lia. ms.  rewrite union_difference_L; ms.
    exch 1. apply ImpLVar_rev. exch 0; exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
      forward. case (decide (ψ = Var p)).
      * intro; subst. forward. exch 0. apply ImpLVar. exch 0.
         do 2 backward. apply (IHh (Var p) Hle) with Hp. lia. ms. ms.
      * intro. forward. exch 0. apply ImpLVar; exch 0; do 2 backward.
         apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∧ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLAnd. apply p_contr.
    apply IHw. simpl in *; lia. ms.  rewrite union_difference_L; ms.
    apply ImpLAnd_rev. exch 0. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLAnd. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∨ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLOr. apply p_contr.
    apply IHw. simpl in *; lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply p_contr.
    apply IHw. simpl in *. lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply ImpLOr_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLOr. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = ((φ1 → φ2) → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLImp.
    * apply ImpR.
      do 3 (exch 0; apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|exch 1]).
      exch 1; apply ImpLImp_dup. (* key lemma *)
      exch 0; exch 1. apply ImpR_rev.
      lazy_apply Hp1. rewrite <- env_replace; ms.
    * apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|].
      apply (ImpLImp_prev _ φ1 φ2 φ3). exch 0.
      peapply Hp2. rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLImp; backward.
    * apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * apply (IHh ψ Hle) with Hp2. lia. ms. ms.
Qed.

Global Hint Resolve contraction : proof.

Theorem generalised_contraction  (Γ Γ' : env) φ:
  Γ' ⊎ Γ' ⊎ Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
revert Γ.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec; intros Γ Hp.
- peapply Hp.
- peapply (contraction (Γ' ⊎ Γ) x). peapply (IHΓ' (Γ•x•x)). peapply Hp.
Qed.

(** ** Admissibility of LJ's implication left rule *)

(** We show that the general implication left rule of LJ is admissible in G4ip.
  This is Proposition 5.2 in (Dyckhoff Negri 2000). *)

Lemma ImpL  Γ φ ψ θ: Γ•(φ → ψ) ⊢ φ -> Γ•ψ  ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof. intros H1 H2. apply contraction, weak_ImpL; auto with proof. Qed.


(* Lemma 5.3 (Dyckhoff Negri 2000) shows that an implication on the left may be
   weakened. *)

Lemma imp_cut  φ Γ ψ θ: Γ•(φ → ψ) ⊢ θ -> Γ•ψ ⊢ θ.
Proof.
intro Hp.
remember (Γ•(φ → ψ)) as Γ0 eqn:HH.
assert (Heq: Γ ≡ Γ0 ∖ {[(φ → ψ)]}) by ms.
assert(Hin : (φ → ψ) ∈ Γ0) by ms. clear HH.
rw Heq 1. clear Heq Γ.
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ0 φ ψ θ Hle Hin Hp.
induction w; intros  Γ φ ψ θ Hle Hin Hp;
 [destruct φ; simpl in Hle; lia|].
induction Hp.
- forward. auto with proof.
- forward. auto with proof.
-apply AndR; intuition.
- forward; apply AndL. exch 0. do 2 backward. apply IHHp; trivial. ms.
- apply OrR1; intuition.
- apply OrR2; intuition.
- forward. apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp; trivial. ms.
- case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward. apply IHHp; ms.
- case (decide ((φ1 ∧ φ2 → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0; subst.
    assert(Heq1 : ((Γ•(φ1 ∧ φ2 → ψ)) ∖ {[φ1 ∧ φ2 → ψ]}) ≡ Γ) by ms;
    rw Heq1 1; clear Heq1. simpl in Hle.
    peapply (IHw (Γ•(φ2 → ψ)) φ2 ψ ψ0); [lia|ms|].
    peapply (IHw (Γ•(φ1 → φ2 → ψ)) φ1 (φ2 → ψ) ψ0); [lia|ms|trivial].
  + forward. apply ImpLAnd. backward. apply IHHp; trivial. ms.
- case (decide ((φ1 ∨ φ2 → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0.
    apply contraction. simpl in Hle.
    peapply (IHw (Γ•ψ•(φ1 → ψ)) φ1 ψ); [lia|ms|].
    exch 0.
    peapply (IHw (Γ•(φ1 → ψ)•(φ2 → ψ)) φ2 ψ); trivial; [lia|ms].
  + forward. apply ImpLOr; exch 0; do 2 backward; apply IHHp; ms.
- case (decide (((φ1 → φ2) → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0. peapply Hp2.
  + forward. apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
Qed.

Global Hint Resolve imp_cut : proof.

Lemma OrR_idemp  Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp; auto with proof. Qed.

(**
  - [var_not_tautology]: A variable cannot be a tautology.
  - [bot_not_tautology]: ⊥ is not a tautology.
*)

Lemma bot_not_tautology  : (∅ ⊢ ⊥) -> False.
Proof.
intro Hf. dependent destruction Hf; simpl in *;
match goal with x : _ ⊎ {[+?φ+]} = _ |- _ =>
exfalso; eapply (gmultiset_elem_of_empty φ); setoid_rewrite <- x; ms end.
Qed.

Lemma var_not_tautology  v: (∅ ⊢ Var v) -> False.
Proof.
intro Hp.
remember ∅ as Γ.
dependent induction Hp;
match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq);
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; ms
  end.
Qed.

(* A tautology is either equal to ⊤ or has a weight of at least 3. *)
Lemma weight_tautology  (φ : form) : (∅ ⊢ φ) -> {φ = ⊤} + {3 ≤ weight φ}.
Proof.
intro Hp.
destruct φ.
- contradict Hp. apply  var_not_tautology.
- contradict Hp. apply bot_not_tautology.
- right. simpl ; destruct φ1 ; destruct φ2 ; cbn ; lia.
- right. simpl ; destruct φ1 ; destruct φ2 ; cbn ; lia.
- right. simpl ; destruct φ1 ; destruct φ2 ; cbn ; lia.
Qed.

Lemma list_conjR : forall l Γ,
  (forall ψ, In ψ l -> Γ ⊢ ψ) ->
  Γ ⊢ (list_conj l).
Proof.
induction l ; cbn ; intros ; auto.
- apply ImpR , BotL.
- apply AndR.
  + apply H ; auto.
  + apply IHl ; intros ψ H0 ; apply H ; right ; auto.
Qed.

Lemma list_conjL : forall l Γ ϕ ψ,
  In ψ l ->
  (Γ • ψ) ⊢ ϕ ->
  Γ • (list_conj l) ⊢ ϕ.
Proof.
induction l ; cbn ; intros ; auto.
- contradiction.
- apply AndL. case (decide (a = ψ)).
  + intro H1 ; subst. apply weakening ; auto.
  + intro H1. exch 0 ; apply weakening. apply IHl with ψ ; auto.
    destruct H ; [ contradiction | auto].
Qed.

Lemma list_disjL : forall l Γ ϕ,
  (forall ψ, In ψ l -> Γ • ψ ⊢ ϕ) ->
  Γ • (list_disj l) ⊢ ϕ.
Proof.
induction l ; cbn ; intros ; auto.
- apply BotL.
- apply OrL.
  + apply H ; auto.
  + apply IHl ; intros ψ H0 ; apply H ; right ; auto.
Qed.

Lemma list_disjR : forall l Γ ψ,
  In ψ l -> 
  Γ ⊢ ψ ->
  Γ ⊢ list_disj l.
Proof.
induction l ; cbn ; intros ; auto.
- contradiction.
- case (decide (a = ψ)).
  + intro H1 ; subst. apply OrR1 ; auto.
  + intro H1. apply OrR2. apply IHl with ψ ; auto.
    destruct H ; [ contradiction | auto].
Qed.

































(* PART 7 : CUT ADMISSIBILITY *)


(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Cut.v *)


(** * Cut Admissibility *)


Local Hint Rewrite @elements_env_add : order.

Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
(* Primary induction on the weight of the cut formula. *)
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
remember (Γ, ψ) as pe.
replace Γ with pe.1 by now subst.
replace ψ with pe.2 by now subst. clear Heqpe Γ ψ. revert pe.
(* Secondary induction via the well-foundnedness of the
   multiset order. *)
refine  (@well_founded_induction _ _ wf_pointed_env_ms_order _ _).
intros (Γ &ψ). simpl. intro IHW'. assert (IHW := fun Γ0 => fun ψ0 => IHW' (Γ0, ψ0)).
simpl in IHW. clear IHW'. intros HPφ HPψ.
Ltac otac Heq := subst; repeat rewrite env_replace in Heq by trivial; repeat rewrite env_add_remove by trivial; order_tac; rewrite Heq; order_tac.
(* We inspect the structure of the proof of the left 
   premise "Γ ⊢G4ip φ". *)
destruct HPφ; simpl in Hw.
- now apply contraction.
- apply BotL.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW; auto with proof. otac Heq.
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW; auto with proof.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
- (* (V) *)
  (* The last rule applied was ImpR, so the cut
     formula is an implication. Here, we need to
     inspect the structure of the proof of the
     other premise. *)
  remember (Γ • (φ → ψ0)) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ φ → ψ0]}) by ms.
  assert(Hin : (φ → ψ0) ∈ Γ')by ms.
  rw Heq 0.
  (* Here, we need to have a look at the structure of the
     proof of the right premise "(Γ • φ) ⊢G4ip ψ". *)
  destruct HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * rw (symmetry Heq) 0. apply IHW.
     -- unfold pointed_env_ms_order. otac Heq.
     -- now apply ImpR.
     -- peapply HPψ1.
     * rw (symmetry Heq) 0. apply IHW.
       -- otac Heq.
       -- apply ImpR. peapply HPφ.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * unfold pointed_env_ms_order. otac Heq.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * rewrite HH, env_add_remove. otac Heq.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * rewrite HH, env_add_remove. otac Heq.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + forward. apply ImpR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ (φ → ψ0))
            by (rw (symmetry (difference_singleton _ (φ0 ∨ψ) Hin')) 0; peapply HPφ).
       assert (HP := (OrL_rev  _ φ0 ψ (φ → ψ0) HPφ')).
       apply OrL.
      * apply IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- otac Heq.
      -- apply weakening, ImpR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + case (decide ((Var p → φ0) = (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'.
         replace ((Γ0 • Var p • (#p → ψ0)) ∖ {[#p → ψ0]}) with (Γ0 • Var p) by ms.
         apply (IHw ψ0).
        -- lia.
        -- apply contraction. peapply HPφ.
        -- assumption.
      * intro Hneq. do 2 forward. exch 0. apply ImpLVar, IHW.
        -- repeat rewrite env_replace in Heq by trivial. otac Heq.
        -- apply imp_cut with (φ := Var p). exch 0. do 2 backward.
            rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0.
         apply (IHw (φ1 → φ2 → ψ0)).
        -- simpl in *. lia.
        -- apply ImpR, ImpR, AndL_rev, HPφ.
        -- peapply HPψ.
      * intro Hneq. forward. apply ImpLAnd, IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- apply ImpLAnd_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + case (decide (((φ1 ∨ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0. apply OrL_rev in HPφ.
         apply (IHw (φ1 → ψ0)).
        -- simpl in *. lia.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply ImpR, HPφ.
           ++ apply weakening, ImpR, HPφ.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply weakening, ImpR, HPφ.
           ++ peapply HPψ.
      * intro Hneq. forward. apply ImpLOr, IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- apply ImpLOr_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ0))).
     * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0. apply (IHw ψ0).
      -- lia.
      -- apply (IHw(φ1 → φ2)).
        ++ lia.
        ++ apply (IHw (φ2 → ψ0)).
            ** simpl in *. lia.
            ** apply ImpR. eapply imp_cut, HPφ.
            ** peapply HPψ1.
        ++ exact HPφ.
    -- peapply HPψ2.
   *  (* (V-d) *)
       intro Hneq. forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ otac Heq.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ otac Heq.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
- apply ImpLVar. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply (imp_cut (Var p)). exch 0; exact HPψ.
- apply ImpLAnd. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHW; eauto.
  + otac Heq.
  + exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHW.
  + otac Heq.
  + assumption.
  + exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
Qed.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.