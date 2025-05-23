(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Environments.v *)

(** * Environments

  An environment is a multiset of formulas. We rely on stdpp multisets
  mostly for their powerful multiset equivalence tactic.*)

(** Notion of wellfoundedness *)
Require Import Coq.Program.Wf.

(** Stdpp implementation of multisets *)
Require Export stdpp.gmultiset.

(** Our propositional formulas, including their countability. *)
Require Export syntax syntax_facts.

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

Lemma env_add_remove : ∀ (Γ: env) φ, (Γ • φ) ∖ {[φ]} =Γ.
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
unfold base.singleton, multisets.singleton. ms.
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
