(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/SequentProps.v *)

Require Import list_sequent.
Require Export stdpp.list.
Require Import Coq.Program.Equality.

(* The issue with lists is that now we do not have
   exchange for free. It is a painful, bureaucratic
   and long proof... *)

Theorem exchange Γ Γ' φ : Γ ≡ₚ Γ' -> Γ ⊢ φ -> Γ' ⊢ φ.
Proof.
Admitted.

(** ** Weakening *)

Theorem weakening  ψ Γ φ : Γ ⊢ φ -> ψ :: Γ ⊢ φ.
Proof.
intro H. revert ψ. induction H ; intro ψ'.
- apply exchange with ((ψ' :: Γ0) ++ # p :: Γ1) ; auto.
  apply Atom.
- apply exchange with ((ψ' :: Γ0) ++ Bot :: Γ1) ; auto.
  apply ExFalso.
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
    apply Atom.
  + apply exchange with ([] ++ Bot :: Γ) ; auto.
    apply ExFalso.
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
      apply ExFalso.
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
   useful when we deal with context which look different but
   are claimed to be equal. *)

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
  + (* Now that we made our # p explicit, we can apply the Atom rule. *)
    apply Atom.
- (* Do the same as above: exhibit Bot, and apply the ExFalso rule on
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

Lemma TopL_rev Γ θ: ⊤ :: Γ ⊢ θ -> Γ ⊢ θ.
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
- apply weakening ; apply ExFalso.
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

(** An auxiliary definition of **height** of a proof, measured along the leftmost branch. *)
Fixpoint height  {Γ φ} (Hp : Γ ⊢ φ) := match Hp with
| Atom _ _ _ => 1
| ExFalso _ _ _ => 1
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

  (* STOPPED HERE *)

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
  + intro; subst. exhibit Hin' 0. apply Atom.
  + intro Hneq. forward. apply Atom.
- case(decide (ψ = ⊥)).
  + intro; subst. exhibit Hin' 0. apply ExFalso.
  + intro. forward. apply ExFalso.
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
- apply ImpR , ExFalso.
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
- apply ExFalso.
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