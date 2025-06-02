(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/SequentProps.v *)

Require Import list_sequent.
Require Export stdpp.list.
Require Import Coq.Program.Equality.

(* We need a standard result but in Type and not in Prop. *)

Lemma in_splitT : ∀ (x : form) (l : list form), In x l →
  {l1 & {l2 & l = l1 ++ x :: l2} }.
Proof.
induction l ; cbn ; intros ; [ contradiction |auto].
destruct (form_eq_dec a x) ; subst.
- exists [], l ; cbn ; auto.
- assert (In x l) by (destruct H ; auto ; contradiction).
  apply IHl in H0 as [l1 [l2 H0]] ; subst.
  exists (a :: l1), l2 ; cbn; auto.
Qed.

Lemma in_app_orT : ∀ (l m : list form) (a : form), In a (l ++ m) → {In a l} + {In a m}.
Proof.
induction l ; cbn ; intros ; auto.
destruct (form_eq_dec a a0) ; subst.
- left ; auto.
- assert (In a0 (l ++ m)) by (destruct H ; auto ; contradiction).
  apply IHl in H0 as [H1 | H1] ; auto.
Qed.

(* The issue with lists is that now we do not have
   exchange for free. If not done set up properly,
   you can really end up in a nightmarish proof
   thousands of lines long (first hand experience
   speaking here...). *)

Theorem exchange Γ Γ' φ : Γ ≡ₚ Γ' -> Γ ⊢ φ -> Γ' ⊢ φ.
Proof.
intros Hper Hp.
revert Γ' Hper.
induction Hp ; subst ; intros Γ' Hper.
- assert (In (# p) Γ').
  { apply Permutation_in with (Γ0 ++ # p :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply PId.
- assert (In ⊥ Γ').
  { apply Permutation_in with (Γ0 ++ ⊥ :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply BotL.
- apply AndR ; auto.
- assert (In (φ ∧ ψ) Γ').
  { apply Permutation_in with (Γ0 ++ (φ ∧ ψ) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply AndL. apply IHHp. repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
  apply Permutation_app_inv in Hper ; auto.
- apply OrR1 ; auto.
- apply OrR2 ; auto.
- assert (In (φ ∨ ψ) Γ').
  { apply Permutation_in with (Γ0 ++ (φ ∨ ψ) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply OrL.
  + apply IHHp1.
    repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
  + apply IHHp2.
    repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
- apply ImpR. apply IHHp. apply Permutation_cons ; auto.
(* Rules below requires, as for the previous left rules, to make
   the principal formulas visible to apply the rule and then
   use the induction hypotheses. *)
- assert (In (# p) Γ').
  { apply Permutation_in with (Γ0 ++ # p :: Γ1 ++ (# p → φ) :: Γ2) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ3 [Γ4 H]] ; subst.
  assert (In (# p → φ) (Γ3 ++ Γ4)).
  { assert (In (# p → φ) (Γ3 ++ # p :: Γ4)).
    apply Permutation_in with (Γ0 ++ # p :: Γ1 ++ (# p → φ) :: Γ2) ; [ auto | apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; split].
    apply in_or_app ; apply in_app_or in H as [H | H] ; auto. inversion H ; [ discriminate | auto]. }
  apply in_app_orT in H as [H | H].
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc.
    apply ImpLVar2. apply IHHp. repeat rewrite <- Permutation_middle.
    rewrite perm_swap. do 2 (apply Permutation_cons ; auto).
    repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
    repeat apply Permutation_cons_inv in Hper. rewrite <- app_assoc in Hper ; auto.
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst.
    apply ImpLVar1. apply IHHp. repeat rewrite <- Permutation_middle.
    do 2 (apply Permutation_cons ; auto).
    repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
    repeat apply Permutation_cons_inv in Hper ; auto.
- assert (In (# p → φ) Γ').
  { apply Permutation_in with (Γ0 ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ3 [Γ4 H]] ; subst.
  assert (In (# p) (Γ3 ++ Γ4)).
  { assert (In (# p) (Γ3 ++ (# p → φ) :: Γ4)).
    apply Permutation_in with (Γ0 ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; [ auto | apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; split].
    apply in_or_app ; apply in_app_or in H as [H | H] ; auto. inversion H ; [ discriminate | auto]. }
  apply in_app_orT in H as [H | H].
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc.
    apply ImpLVar1. apply IHHp. repeat rewrite <- Permutation_middle.
    rewrite perm_swap. do 2 (apply Permutation_cons ; auto).
    repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
    repeat apply Permutation_cons_inv in Hper. rewrite <- app_assoc in Hper ; auto.
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst.
    apply ImpLVar2. apply IHHp. repeat rewrite <- Permutation_middle.
    do 2 (apply Permutation_cons ; auto).
    repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
    repeat apply Permutation_cons_inv in Hper ; auto.
- assert (In (φ1 ∧ φ2 → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply ImpLAnd. apply IHHp. apply Permutation_app_inv in Hper.
  do 2 (rewrite <- Permutation_middle). apply Permutation_cons ; auto. 
- assert (In (φ1 ∨ φ2 → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply ImpLOr. apply IHHp. apply Permutation_app_inv in Hper.
  do 4 (rewrite <- Permutation_middle). apply Permutation_cons ; auto.
- assert (In ((φ1 → φ2) → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ ((φ1 → φ2) → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  apply ImpLImp.
  + apply IHHp1. apply Permutation_app_inv in Hper.
    do 2 (rewrite <- Permutation_middle). apply Permutation_cons ; auto.
  + apply IHHp2. apply Permutation_app_inv in Hper.
    do 2 (rewrite <- Permutation_middle). apply Permutation_cons ; auto.
Qed.

(** ** Weakening *)

Theorem weakening  ψ Γ φ : Γ ⊢ φ -> ψ :: Γ ⊢ φ.
Proof.
intro H. revert ψ. induction H ; intro ψ'.
(* The proofs here do not rely multisets anymore,
   so we cannot use the powerful ms tactic which automatically
   shows that two multisets are the same. Now, we need
   to explicitly use exchange and show that indeed the
   two lists are permutations of each other.
   This makes the proofs longer. *)
- apply exchange with ((ψ' :: Γ0) ++ # p :: Γ1) ; auto.
  apply PId.
- apply exchange with ((ψ' :: Γ0) ++ Bot :: Γ1) ; auto.
  apply BotL.
- apply AndR ; auto.
- apply exchange with ((ψ' :: Γ0) ++ (φ ∧ ψ) :: Γ1) ; auto.
  apply AndL ; cbn ; auto.
- apply OrR1 ; auto.
- apply OrR2 ; auto.
- apply exchange with ((ψ' :: Γ0) ++ (φ ∨ ψ) :: Γ1) ; auto.
  apply OrL ; cbn ; auto.
- apply ImpR. apply exchange with (ψ' :: φ :: Γ) ; auto.
  apply perm_swap.
- apply exchange with ((ψ' :: Γ0) ++ # p :: Γ1 ++ (# p → φ) :: Γ2) ; auto.
  apply ImpLVar1 ; cbn ; auto.
- apply exchange with ((ψ' :: Γ0) ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; auto.
  apply ImpLVar2 ; cbn ; auto.
- apply exchange with ((ψ' :: Γ0) ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLAnd ; cbn ; auto.
- apply exchange with ((ψ' :: Γ0) ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLOr ; cbn ; auto.
- apply exchange with ((ψ' :: Γ0) ++ ((φ1 → φ2) → φ3) :: Γ1) ; auto.
  apply ImpLImp ; cbn ; auto.
Qed.
 
Global Hint Resolve weakening : proof.

Theorem generalised_weakeningL  Γ Γ' φ: Γ ⊢ φ -> Γ' ++ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ' as [| x Γ' IHΓ'] ; auto.
cbn. apply (weakening x). exact IHΓ'.
Qed.

Theorem generalised_weakeningR  Γ Γ' φ: Γ' ⊢ φ -> Γ' ++ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ as [| x Γ IHΓ].
- rewrite app_nil_r ; auto.
- apply exchange with (x :: Γ' ++ Γ).
  + apply Permutation_middle.
  + apply (weakening x). exact IHΓ.
Qed.

(** ** Inversion rules *)

(** We prove that the following rules are invertible: implication right, and
  left, or left, top left (i.e., the appliction of weakening for the formula
  top), the four implication left rules, the and right rule and the application of the or right rule with bottom. *)

Lemma ImpR_rev  Γ φ ψ :
  (Γ ⊢ (φ →  ψ))
    -> φ :: Γ ⊢  ψ.
Proof with (auto with proof).
intro Hp. remember (φ → ψ) as χ.
revert φ ψ Heqχ. induction Hp; intros φ' ψ' Heq ;
auto with proof ; try discriminate.
- apply exchange with ((φ' :: Γ0) ++ (φ ∧ ψ) :: Γ1) ; auto.
  apply AndL ; cbn ; auto.
- apply exchange with ((φ' :: Γ0) ++ (φ ∨ ψ) :: Γ1) ; auto.
  apply OrL ; cbn ; auto.
- inversion Heq ; subst ; auto.
- apply exchange with ((φ' :: Γ0) ++ # p :: Γ1 ++ (# p → φ) :: Γ2) ; auto.
  apply ImpLVar1 ; cbn ; auto.
- apply exchange with ((φ' :: Γ0) ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; auto.
  apply ImpLVar2 ; cbn ; auto.
- apply exchange with ((φ' :: Γ0) ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLAnd ; cbn ; auto.
- apply exchange with ((φ' :: Γ0) ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLOr ; cbn ; auto.
- subst. apply exchange with ((φ' :: Γ0) ++ ((φ1 → φ2) → φ3) :: Γ1) ; auto.
  apply ImpLImp ; cbn ; auto. apply ImpR.
  apply exchange with (φ' :: φ1 :: Γ0 ++ (φ2 → φ3) :: Γ1) ; auto.
  + apply perm_swap.
  + apply weakening ; auto.
Qed.

Global Hint Resolve ImpR_rev : proof.

Theorem generalised_axiom  Γ φ : φ :: Γ ⊢ φ.
Proof with (auto with proof).
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ φ Hle.
induction w; intros Γ φ Hle.
- destruct φ ; cbn in Hle ; lia.
- destruct φ; simpl in Hle...
  + apply exchange with ([] ++ # n :: Γ) ; auto.
    apply PId.
  + apply exchange with ([] ++ Bot :: Γ) ; auto.
    apply BotL.
  + apply exchange with ([] ++ (φ1 ∧ φ2) :: Γ) ; auto.
    apply AndL,AndR ; cbn.
    * apply IHw ; lia.
    * apply weakening. apply IHw ; lia.
  + apply exchange with ([] ++ (φ1 ∨ φ2) :: Γ) ; auto.
    apply OrL ; cbn.
    * apply OrR1 ; apply IHw ; lia.
    * apply OrR2 ; apply IHw ; lia.
  + apply ImpR. destruct φ1.
    * apply exchange with ([] ++ # n :: [] ++ (# n → φ2) :: Γ) ; auto.
      apply ImpLVar1 ; cbn ; apply weakening ; apply IHw ; lia.
    * apply exchange with ([] ++ Bot :: (Bot → φ2) :: Γ) ; auto.
      apply BotL.
    * apply exchange with ([(φ1_1 ∧ φ1_2)] ++ (φ1_1 ∧ φ1_2 → φ2) :: Γ) ; auto.
      apply ImpLAnd. cbn. 
      apply exchange with ([] ++ (φ1_1 ∧ φ1_2) :: (φ1_1 → φ1_2 → φ2) :: Γ) ; auto.
      apply AndL ; cbn.
      apply exchange with ( φ1_2 :: φ1_1 :: (φ1_1 → φ1_2 → φ2) :: Γ) ; auto.
      -- apply perm_swap.
      -- do 2 (apply ImpR_rev) ; apply IHw ; cbn in * ; lia.
    * apply exchange with ([(φ1_1 ∨ φ1_2)] ++ (φ1_1 ∨ φ1_2 → φ2) :: Γ) ; auto.
      apply ImpLOr. cbn. 
      apply exchange with ([] ++ (φ1_1 ∨ φ1_2) :: (φ1_1 → φ2) :: (φ1_2 → φ2) :: Γ) ; auto.
      apply OrL ; cbn.
      -- apply ImpR_rev ; apply IHw ; cbn in * ; lia.
      -- apply ImpR_rev ; apply weakening ; apply IHw ; cbn in * ; lia.
    * apply exchange with ([(φ1_1 → φ1_2)] ++ ((φ1_1 → φ1_2) → φ2) :: Γ) ; auto.
      apply ImpLImp. cbn.
      -- apply IHw ; auto ; cbn in * ; lia.
      -- cbn ; apply weakening ; apply IHw ; cbn in * ; lia.
Qed.

Global Hint Resolve generalised_axiom : proof.

(* If a formula is in a list, we can find a permutation of
   the list which exhibits the formula. This lemma is very
   useful when we deal with contexts which look different but
   are claimed to be equal / permutations of each other. *)

Lemma in_Permutation (Γ : list form) φ : In φ Γ -> { Γ' | φ :: Γ' ≡ₚ Γ}.
Proof.
induction Γ ; cbn ; intros ; [ contradiction | ].
destruct (form_eq_dec a φ) ; subst.
- exists Γ ; auto.
- assert (H0 : In φ Γ) by (destruct H ; [ contradiction | auto]).
  apply IHΓ in H0. destruct H0. exists (a :: x).
  transitivity (a :: φ :: x) ; [apply perm_swap | ].
  apply Permutation_cons ; auto.
Qed.

Lemma AndL_rev  Γ φ ψ θ: (φ ∧ ψ) :: Γ ⊢ θ  → φ :: ψ :: Γ ⊢ θ.
Proof.
intro Hp.
remember ((φ ∧ ψ) :: Γ) as Γ' eqn:HH.
revert φ ψ Γ HH.
induction Hp; intros φ0 ψ0 Γ' Heq ; auto with proof.
- (* As # p is hidden in Γ', we use in_Permutation to make it 
     explicit. So, we need to explicitly prove that it is in Γ'. *)
  assert (In (# p) Γ').
  { assert (In (# p) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  (* Then we can apply our lemma to exhibit # p. *)
  apply in_Permutation in H as [Γ'' H].
  (* At this point we know that our context is a permutation
     of the context given in the next line. *)
  apply exchange with ([φ0 ; ψ0] ++ # p :: Γ'') ; auto.
  + cbn ; do 2 (apply Permutation_cons ; auto).
  + (* Now that we made our # p explicit, we can apply the PId rule. *)
    apply PId.
- (* Do the same as above: exhibit Bot, and apply the BotL rule on
     the propertly structured context. *) admit.
(* the main case *)
- (* Here we do not know whether (φ ∧ ψ) is the same conjunction 
     as (φ0 ∧ ψ0). So, we make a case distinction. *)
  case(decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0. 
  (* If they are the same *)
  + inversion Heq0 ; subst. eapply exchange ; [ | exact Hp].
    transitivity (φ0 :: ψ0 :: Γ0 ++ Γ1).
    * symmetry. apply Permutation_cons_app. apply Permutation_middle.
    * do 2 (apply Permutation_cons ; auto). apply Permutation_cons_inv with (φ0 ∧ ψ0).
      rewrite <- Heq. apply Permutation_middle.
  (* If they are not *)
  + (* Here again, we need to exhibit the conjunction and then apply the rule. *) admit.
(* All remaining cases require that we exhibit the adequate formula in order
   to apply the rule. *)
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
Admitted.

Lemma OrL_rev  Γ φ ψ θ: (φ ∨ ψ) :: Γ ⊢ θ  → (φ :: Γ ⊢ θ) * (ψ :: Γ ⊢ θ).
Proof.
(* Copy-paste the proof above, and modify it to work with the current
   setup. The proofs are very similar. *)  
Admitted.

Lemma TopL_rev Γ θ : ⊤ :: Γ ⊢ θ -> Γ ⊢ θ.
Proof.
Admitted.

Local Hint Immediate TopL_rev : proof.

Lemma ImpLVar_rev  Γ p φ ψ: (# p) :: (# p → φ) :: Γ ⊢ ψ  → (# p) :: φ :: Γ ⊢ ψ.
Proof.
Admitted.

(* inversion for ImpLImp is only partial *)
Lemma ImpLImp_prev  Γ φ1 φ2 φ3 ψ: ((φ1 → φ2) → φ3) :: Γ ⊢ ψ -> φ3 :: Γ ⊢ ψ.
Proof.
Admitted.

Lemma ImpLOr_rev  Γ φ1 φ2 φ3 ψ:
  ((φ1 ∨ φ2) → φ3) :: Γ ⊢ ψ -> (φ1 → φ3) :: (φ2 → φ3) :: Γ ⊢ ψ.
Proof.
Admitted.

Lemma ImpLAnd_rev  Γ φ1 φ2 φ3 ψ: (φ1 ∧ φ2 → φ3) :: Γ ⊢ ψ ->  (φ1 → φ2 → φ3) :: Γ ⊢ ψ .
Proof.
Admitted.

Global Hint Resolve AndL_rev : proof.
Global Hint Resolve OrL_rev : proof.
Global Hint Resolve ImpLVar_rev : proof.
Global Hint Resolve ImpLOr_rev : proof.
Global Hint Resolve ImpLAnd_rev : proof.


Lemma exfalso  Γ φ: Γ ⊢ ⊥ -> Γ ⊢ φ.
Proof.
intro Hp. dependent induction Hp; try tauto; auto with proof.
Qed.

Global Hint Immediate exfalso : proof.

Lemma AndR_rev  {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ1) * (Γ ⊢ φ2).
Proof.
  intro Hp. dependent induction Hp generalizing φ1 φ2 Hp;
  try specialize (IHHp _ _ eq_refl);
  try specialize (IHHp1 _ _ eq_refl);
  try specialize (IHHp2 _ _ eq_refl);
  intuition; auto with proof.
Qed.


(** A general inversion rule for disjunction is not admissible. However, inversion holds if one of the formulas is ⊥. *)

Lemma OrR1Bot_rev  Γ φ :  Γ ⊢ φ ∨ ⊥ -> Γ ⊢ φ.
Proof. intro Hd.
 dependent induction Hd generalizing φ; auto using exfalso with proof. Qed.

Lemma OrR2Bot_rev  Γ φ :  Γ ⊢ ⊥ ∨ φ -> Γ ⊢ φ.
Proof. intro Hd. dependent induction Hd; auto using exfalso with proof. Qed.


(** The classical left implication rule is admissible. *)

Lemma weak_ImpL  Γ φ ψ θ : Γ ⊢ φ -> ψ :: Γ ⊢ θ -> (φ → ψ) :: Γ ⊢ θ.
Proof with (auto with proof).
intro Hp. revert ψ θ. induction Hp ; intros ψ0 θ0 Hp'.
- apply exchange with ([] ++ (# p → ψ0) :: Γ0 ++ # p :: Γ1) ; auto.
  apply ImpLVar2 ; auto.
- apply weakening ; apply BotL.
- apply exchange with ([] ++ (φ ∧ ψ → ψ0) :: Γ) ; auto.
  apply ImpLAnd ; cbn. apply IHHp1,IHHp2 ; auto.
- apply exchange with (((θ → ψ0) :: Γ0) ++ (φ ∧ ψ) :: Γ1) ; auto.
  apply AndL. apply IHHp.
  apply exchange with (φ :: ψ :: (ψ0 :: Γ0 ++ Γ1)) ; auto.
  + transitivity ((ψ0 :: Γ0) ++ [φ ; ψ] ++ Γ1) ; auto.
    rewrite <- Permutation_app_swap_app ; auto.
  + apply AndL_rev. eapply exchange ; [ | exact Hp' ].
    transitivity ((ψ0 :: Γ0) ++ (φ ∧ ψ) :: Γ1) ; auto.
    rewrite <- Permutation_middle. auto.
- apply exchange with ([] ++ (φ ∨ ψ → ψ0) :: Γ) ; auto.
  apply ImpLOr ; cbn.
  apply exchange with ((ψ → ψ0) :: (φ → ψ0) :: Γ) ; auto.
  + apply perm_swap.
  + apply weakening,IHHp ; auto.
- apply exchange with ([] ++ (φ ∨ ψ → ψ0) :: Γ) ; auto.
  apply ImpLOr ; cbn. apply weakening,IHHp ; auto.
- apply exchange with (((θ → ψ0) :: Γ0) ++ (φ ∨ ψ) :: Γ1) ; auto.
  apply OrL.
  + cbn. apply IHHp1. apply exchange with (φ :: ψ0 :: Γ0 ++ Γ1) ; auto.
    * pose (Permutation_middle (ψ0 :: Γ0) Γ1) ; cbn in p ; auto.
    * edestruct OrL_rev as [H0 H1] ; [ | exact H0].
      eapply exchange ; [ | exact Hp']. symmetry.
      pose (Permutation_middle (ψ0 :: Γ0) Γ1) ; cbn in p ; apply p.
  + cbn. apply IHHp2. apply exchange with (ψ :: ψ0 :: Γ0 ++ Γ1) ; auto.
    * pose (Permutation_middle (ψ0 :: Γ0) Γ1) ; cbn in p ; auto.
    * edestruct OrL_rev as [H0 H1] ; [ | exact H1].
      eapply exchange ; [ | exact Hp']. symmetry.
      pose (Permutation_middle (ψ0 :: Γ0) Γ1) ; cbn in p ; apply p.
- apply exchange with ([] ++ ((φ → ψ) → ψ0) :: Γ) ; auto.
  apply ImpLImp ; cbn ; auto. apply ImpR.
  eapply exchange ; [ | apply IHHp ; apply weakening ; exact Hp].
  apply perm_swap.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ # p :: Γ1 ++ (# p → φ) :: Γ2) ; auto.
  apply ImpLVar1 ; cbn ; auto. apply IHHp.
  eapply exchange ; [ | apply ImpLVar_rev ; eapply exchange ; [ | exact Hp']].
  + transitivity ((ψ0 :: Γ0) ++ # p :: Γ1 ++ φ :: Γ2) ; auto.
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | ].
    transitivity ((ψ0 :: Γ0 ++ Γ1) ++ φ :: Γ2).
    * rewrite <- Permutation_middle. cbn ; repeat rewrite <- app_assoc ; reflexivity.
    * cbn ; repeat rewrite <- app_assoc ; auto.
  + transitivity ((ψ0 :: Γ0) ++ # p :: Γ1 ++ (# p → φ) :: Γ2 ) ; auto.
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | ].
    transitivity ((ψ0 :: Γ0 ++ Γ1) ++ (# p → φ) :: Γ2).
    * cbn ; repeat rewrite <- app_assoc ; auto.
    * rewrite <- Permutation_middle. cbn ; repeat rewrite <- app_assoc ; reflexivity.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; auto.
  apply ImpLVar2 ; cbn ; auto. apply IHHp.
  eapply exchange ; [ | apply ImpLVar_rev ; eapply exchange ; [ | exact Hp']].
  + transitivity ((ψ0 :: Γ0 ++ φ :: Γ1) ++ # p :: Γ2) ; [ | cbn ; repeat rewrite <- app_assoc ; auto].
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | ].
    transitivity ((ψ0 :: Γ0) ++ φ :: Γ1 ++ Γ2).
    * rewrite <- Permutation_middle. cbn ; repeat rewrite <- app_assoc ; reflexivity.
    * cbn ; repeat rewrite <- app_assoc ; auto.
  + transitivity ((ψ0 :: Γ0 ++ (# p → φ) :: Γ1) ++ # p :: Γ2 ) ; [ cbn ; repeat rewrite <- app_assoc ; auto | ].
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | ].
    transitivity ((ψ0 :: Γ0) ++ (# p → φ) :: Γ1 ++ Γ2).
    * cbn ; repeat rewrite <- app_assoc ; auto.
    * rewrite <- Permutation_middle. cbn ; repeat rewrite <- app_assoc ; reflexivity.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLAnd ; cbn ; auto. apply IHHp. 
  eapply exchange ; [ | apply ImpLAnd_rev ; eapply exchange ; [ | exact Hp']].
  + transitivity ((ψ0 :: Γ0) ++ (φ1 → φ2 → φ3) :: Γ1) ; auto. apply Permutation_middle.
  + transitivity ((ψ0 :: Γ0) ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; auto. symmetry ; apply Permutation_middle.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; auto.
  apply ImpLOr ; cbn ; auto. apply IHHp. 
  eapply exchange ; [ | apply ImpLOr_rev ; eapply exchange ; [ | exact Hp']].
  + transitivity ((ψ0 :: Γ0) ++ (φ1 → φ3) :: (φ2 → φ3) :: Γ1) ; auto.
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | ].
    rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | reflexivity].
  + transitivity ((ψ0 :: Γ0) ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; auto. symmetry ; apply Permutation_middle.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ ((φ1 → φ2) → φ3) :: Γ1) ; auto.
  apply ImpLImp ; cbn ; auto.
  + apply weakening ; auto. 
  + apply IHHp2. eapply exchange ; [ | eapply ImpLImp_prev ; eapply exchange ; [ | exact Hp']].
    * transitivity (((ψ0) :: Γ0) ++ φ3 :: Γ1) ; auto.
      rewrite <- Permutation_middle. apply Permutation_cons ; [ reflexivity | cbn ; reflexivity ].
    * transitivity ((ψ0 :: Γ0) ++ ((φ1 → φ2) → φ3) :: Γ1) ; auto. rewrite <- Permutation_middle ; cbn.
      apply Permutation_cons ; auto.
Qed.

Global Hint Resolve weak_ImpL : proof.

(** ** Contraction

 The aim of this section is to prove that the contraction rule is admissible in
 G4ip. *)

(** An auxiliary definition of **height** of a proof.
    Note that we would not be able to define this notion
    if we had "Provable" in "Prop" and not in "Type". *)
Fixpoint height  {Γ φ} (Hp : Γ ⊢ φ) :=
match Hp with
| PId _ _ _ => 1
| BotL _ _ _ => 1
| AndR Γ φ ψ H1 H2 => 1 + height H1 + height H2
| AndL Γ0 Γ1 φ ψ θ H => 1 + height H
| OrR1 Γ φ ψ H => 1 + height H
| OrR2 Γ φ ψ H => 1 + height H
| OrL Γ0 Γ1 φ ψ θ H1 H2 => 1 + height H1 + height H2
| ImpR Γ φ ψ H => 1 + height H
| ImpLVar1 Γ0 Γ1 Γ2 p φ ψ H => 1 + height H
| ImpLVar2 Γ0 Γ1 Γ2 p φ ψ H => 1 + height H
| ImpLAnd Γ0 Γ1 φ1 φ2 φ3 ψ H => 1 + height H
| ImpLOr Γ0 Γ1 φ1 φ2 φ3 ψ H => 1 + height H
| ImpLImp Γ0 Γ1 φ1 φ2 φ3 ψ H1 H2 => 1 + height H1 + height H2
end.

Lemma height_0  {Γ φ} (Hp : Γ ⊢ φ) : height Hp <> 0.
Proof. destruct Hp; simpl; lia. Qed.

(* We need a height-preserving version of exchange.
   The reason for this is that we prove some of
   our results by induction on the height of proofs,
   and in some intermediate steps we will need to
   rearrange our context to apply the adequate rule / 
   induction hypothesis. 
   
   Of course, this height-preserving admissibility
   of exchange holds. But again, it is painful to prove.
   To avoid repetitions, one should prove "exchange_hp"
   first, and then prove "exchange" as a corollary. *)

Theorem exchange_hp Γ Γ' φ (Hp: Γ ⊢ φ) : Γ ≡ₚ Γ' ->
      {Hp' : Γ' ⊢ φ | height Hp' <= height Hp} .
Proof.
Admitted.

(* Weakening is also hp *)

Theorem weakening_hp Γ φ (Hp: Γ ⊢ φ) ψ:
      {Hp' : ψ :: Γ ⊢ φ | height Hp' <= height Hp} .
Proof.
Admitted.

(* We can also prove that invertibility of some rules are hp. *)

Lemma AndL_rev_hp Γ φ ψ θ (Hp : (φ ∧ ψ) :: Γ ⊢ θ) :
      { Hp' : φ :: ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma OrL_rev_hp  Γ φ ψ θ (Hp : (φ ∨ ψ) :: Γ ⊢ θ) :
      { Hp' : φ :: Γ ⊢ θ | height Hp' <= height Hp} *
      { Hp' : ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLAnd_rev_hp Γ φ1 φ2 φ3 ψ (Hp : (φ1 ∧ φ2 → φ3) :: Γ ⊢ ψ) :
      { Hp' : (φ1 → φ2 → φ3) :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLOr_rev_hp Γ φ1 φ2 φ3 ψ (Hp : (φ1 ∨ φ2 → φ3) :: Γ ⊢ ψ) :
      { Hp' : (φ1 → φ3) :: (φ2 → φ3) :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLImp_rev_hp Γ φ1 φ2 φ3 ψ (Hp : ((φ1 → φ2) → φ3) :: Γ ⊢ ψ) :
      { Hp' : φ3 :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

(** Lemma 4.2 in (Dyckhoff & Negri 2000), showing that a "duplication" in the context of the implication-case of the implication-left rule is admissible. *)
 
Lemma ImpLImp_dup  Γ φ1 φ2 φ3 θ:
  ((φ1 → φ2) → φ3) :: Γ ⊢ θ ->
    φ1 :: (φ2 → φ3) :: (φ2 → φ3) :: Γ ⊢ θ.
Proof.
intro Hp.
remember (((φ1 → φ2) → φ3) :: Γ) as Γ0 eqn:Heq0.
(* by induction on the height of the derivation *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ Γ0 θ Hp Hleh Heq0. induction h as [|h]; intros Γ' Γ'' θ Hp Hleh Heq0;
[pose (height_0 Hp); lia|].
destruct Hp; cbn in Hleh ; subst.
- (* p is in Γ, so PId *) admit.
- (* Bot is in Γ, so BotL *) admit.
- subst ; apply AndR.
  + eapply (IHh _ _ _ Hp1) ; [ lia | reflexivity].
  + eapply (IHh _ _ _ Hp2) ; [ lia | reflexivity].
- admit.
- subst ; apply OrR1. eapply (IHh _ _ _ Hp) ; [ lia | reflexivity].
- subst ; apply OrR2. eapply (IHh _ _ _ Hp) ; [ lia | reflexivity].
- admit.
- subst ; apply ImpR. edestruct (exchange_hp _ (((φ1 → φ2) → φ3) :: φ :: Γ') _ Hp) as [Hp' Hle].
  + admit.
  + eapply exchange ; [ | eapply (IHh _ _ _ Hp') ; [ lia | reflexivity]].
    admit.
- admit.
- admit.
- admit.
- admit.
- admit.
Admitted.

(** Admissibility of contraction in G4ip. *)
Lemma contraction  Γ ψ θ : ψ :: ψ :: Γ ⊢ θ -> ψ :: Γ ⊢ θ.
Proof.
remember (ψ :: ψ :: Γ) as Γ0 eqn:Heq0.
(* by induction on the weight of ψ *)
remember (weight ψ) as w.
assert(Hle : weight ψ ≤ w) by lia.
clear Heqw. revert Γ Γ0 ψ θ Hle Heq0.
induction w; intros Γ Γ' ψ θ Hle Heq0 Hp; [destruct ψ; simpl in Hle; lia|].
(* by induction on the height of the premise *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ Γ' θ Hp Hleh Heq0. revert ψ Hle; induction h as [|h]; intros ψ Hle Γ Γ' θ Hp Hleh Heq0 ;
[pose (height_0 Hp); lia|].

destruct Hp; simpl in Hleh, Hle ; subst.
- case(decide (ψ = Var p)).
  + intro; subst. apply generalised_axiom.
  + intro Hneq. (* Need to make p appear in Γ *) admit.
- case(decide (ψ = ⊥)).
  + intro; subst. (* exchange then Exfalso *) admit.
  + intro. (* Need to make ⊥ appear in Γ *) admit.
- subst ; apply AndR.
  + eapply (IHh _ _ _ _) with Hp1 ; auto. lia.
  + eapply (IHh _ _ _ _) with Hp2 ; auto. lia.
- case (decide (ψ = (φ ∧ ψ0))); intro Heq.
  + subst. admit.
  + (* Make (φ ∧ ψ0) appear in Γ, apply IHh with exchanges and Hp *) admit.
- apply OrR1. eapply (IHh ψ Hle _ _ _ Hp) ; [ lia | reflexivity].
- apply OrR2. eapply (IHh ψ Hle _ _ _ Hp) ; [ lia | reflexivity].
- case (decide (ψ = (φ ∨ ψ0))); intro Heq.
  + subst. apply exchange with ([] ++ (φ ∨ ψ0) :: Γ) ; auto.
    apply OrL ; cbn.
    * (* Need to make (φ ∨ ψ0) appear in Γ0 ++ Γ1, following Heq0,
         then apply the invertibility of OrL in Hp1, to finally
         contract the two φ in the context and get the desired
         goal (modulo exchange). *) admit.
    * (* Need to make (φ ∨ ψ0) appear in Γ0 ++ Γ1, following Heq0,
         then apply the invertibility of OrL in Hp2, to finally
         contract the two ψ in the context and get the desired
         goal (modulo exchange). *) admit.
  + (* Make (φ ∨ ψ0) appear in Γ, then apply OrL, and finally 
       apply IHh with exchanges and Hp1 and Hp2 respectively *) admit.
- apply ImpR. edestruct (exchange_hp _ (ψ :: ψ :: φ :: Γ) _ Hp) as [Hp' Hle'].
  + rewrite <- perm_swap ; apply Permutation_cons ; auto ; apply perm_swap.
  + eapply exchange ; [ apply perm_swap | eapply (IHh ψ Hle _ _ _ Hp') ; [ lia | reflexivity]].
- case (decide (ψ = (#p → φ))); intro Heq.
  + admit.
  + admit.
- admit.
- admit.
- admit.
- admit.
Admitted.

Global Hint Resolve contraction : proof.

Theorem generalised_contraction  Γ Γ' φ:
  Γ' ++ Γ' ++ Γ ⊢ φ -> Γ' ++ Γ ⊢ φ.
Proof.
revert Γ.
induction Γ' as [| x Γ' IHΓ']; intros Γ Hp ; cbn in * ; auto.
apply contraction. apply exchange with (Γ' ++ x :: x :: Γ).
- do 2 (rewrite <- Permutation_middle) ; auto.
- apply IHΓ'. eapply (exchange _ _ _ _ Hp).
  Unshelve. repeat rewrite <- Permutation_middle ; auto.
Qed.

(** ** Admissibility of LJ's implication left rule *)

(** We show that the general implication left rule of LJ is admissible in G4ip.
  This is Proposition 5.2 in (Dyckhoff Negri 2000). *)

Lemma ImpL Γ φ ψ θ: (φ → ψ) :: Γ ⊢ φ -> ψ :: Γ ⊢ θ -> (φ → ψ) :: Γ ⊢ θ.
Proof. intros H1 H2. apply contraction, weak_ImpL; auto with proof. Qed.


(* Lemma 5.3 (Dyckhoff Negri 2000) shows that an implication on the left may be
   weakened. *)

Lemma imp_cut : forall φ Γ ψ θ, (φ → ψ) :: Γ ⊢ θ -> ψ :: Γ ⊢ θ.
Proof.
(* We need to manage a bit our goal so that we can
   more freely use permutations / exchange. *)
enough (forall Γ' θ, Γ' ⊢G4ip θ -> forall φ Γ ψ, Γ' ≡ₚ (φ → ψ) :: Γ -> ψ :: Γ ⊢G4ip θ).
- intros. apply H with ((φ → ψ) :: Γ) φ ; auto.
- intros Γ' θ Hp φ Γ ψ HH.
  remember (weight φ) as w.
  assert(Hle : weight φ ≤ w) by lia.
  clear Heqw. revert Γ Γ' φ ψ θ Hle HH Hp.
  induction w ; [intros Γ Γ' φ ψ θ Hle HH Hp; destruct φ; simpl in Hle; lia|].
  intros Γ Γ' φ ψ θ Hle HH Hp. revert Γ HH.
  induction Hp ; intros Γ' HH ; subst.
  + destruct (in_Permutation Γ' (# p)).
    * assert (In # p ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * apply exchange with ([ψ] ++ # p :: x).
      -- cbn ; apply Permutation_cons ; auto.
      -- apply PId.
  + destruct (in_Permutation Γ' ⊥).
    * assert (In ⊥ ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * apply exchange with ([ψ] ++ ⊥ :: x).
      -- cbn ; apply Permutation_cons ; auto.
      -- apply BotL.
  + apply AndR ; auto.
  + destruct (in_Permutation Γ' (φ0 ∧ ψ0)).
    * assert (In (φ0 ∧ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * apply exchange with ([ψ] ++ (φ0 ∧ ψ0) :: x).
      -- cbn ; apply Permutation_cons ; auto.
      -- apply AndL ; cbn.
         apply IHHp. (* Follows from "HH" and "p". *) admit.
  + apply OrR1 ; auto.
  + apply OrR2 ; auto.
  + destruct (in_Permutation Γ' (φ0 ∨ ψ0)).
    * assert (In (φ0 ∨ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * apply exchange with ([ψ] ++ (φ0 ∨ ψ0) :: x).
      -- cbn ; apply Permutation_cons ; auto.
      -- apply OrL ; cbn.
        ++ apply IHHp1. (* Follows from "HH" and "p". *) admit.
        ++ apply IHHp2. (* Follows from "HH" and "p". *) admit.
  + apply ImpR. apply exchange with (ψ :: φ0 :: Γ') ; [ apply perm_swap |].
    apply IHHp. (* Follows from "HH". *) admit.
  + case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply exchange with (Γ0 ++ # p :: Γ1 ++ ψ :: Γ2) ; auto.
      (* Follows from "HH". *) admit.
    * (* Need to exhibit "(# p → φ0)" and "# p" in "Γ'" and
         apply ImpVar1, and then apply "IHHp". *) admit.
  + (* We do similarly as in the previous case. *) admit.
  + case (decide ((φ1 ∧ φ2 → φ3) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply (IHw _ ((φ2 → ψ) :: Γ') φ2) ; auto.
      -- cbn in Hle ; lia.
      -- apply (IHw _ ((φ1 → φ2 → ψ) :: Γ') φ1) ; auto.
        ++ cbn in Hle ; lia.
        ++ apply exchange with (Γ0 ++ (φ1 → φ2 → ψ) :: Γ1) ; auto.
           (* Follows from "HH". *) admit.
    * (* Need to exhibit "(φ1 ∧ φ2 → φ3)" in "Γ'" and
         apply ImpLAnd, and then apply "IHHp". *) admit.
(* We proceed as in the previous cases for the remaining ones. *)
  + admit.
  + admit.
Admitted.

Global Hint Resolve imp_cut : proof.

Lemma imp_cut_hp : forall φ Γ ψ θ (Hp : (φ → ψ) :: Γ ⊢ θ),
    { Hp' : ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma OrR_idemp  Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp; auto with proof. Qed.

Lemma list_conjR : forall l Γ,
  (forall ψ, In ψ l -> Γ ⊢ ψ) ->
  Γ ⊢ (list_conj l).
Proof.
induction l ; cbn ; intros ; auto.
- apply ImpR. eapply exchange with ([] ++ Bot :: Γ) ; [ auto | apply BotL].
- apply AndR.
  + apply H ; auto.
  + apply IHl ; intros ψ H0 ; apply H ; right ; auto.
Qed.

Lemma list_conjL : forall l Γ ϕ ψ,
  In ψ l ->
  ψ :: Γ ⊢ ϕ ->
  (list_conj l) :: Γ ⊢ ϕ.
Proof.
induction l ; cbn ; intros ; auto.
- contradiction.
- eapply exchange with ([] ++ (a ∧ list_conj l) :: Γ) ; [ auto | apply AndL].
  case (decide (a = ψ)).
  + intro H1 ; subst ; cbn.
    eapply exchange with (list_conj l :: ψ :: Γ) ; [ apply perm_swap | apply weakening ; auto].
  + intro H1. apply weakening. apply IHl with ψ ; auto.
    destruct H ; [ contradiction | auto].
Qed.

Lemma list_disjL : forall l Γ ϕ,
  (forall ψ, In ψ l -> ψ :: Γ ⊢ ϕ) ->
  (list_disj l) :: Γ ⊢ ϕ.
Proof.
induction l ; cbn ; intros ; auto.
- eapply exchange with ([] ++ Bot :: Γ) ; [ auto | apply BotL].
- eapply exchange with ([] ++ (a ∨ list_disj l) :: Γ) ; [ auto | apply OrL].
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
