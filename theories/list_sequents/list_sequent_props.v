(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/SequentProps.v *)

Require Import list_sequent.
Require Export stdpp.list.
From Stdlib Require Import Program.Equality.

(* We need a standard result but in Type and not in Prop. *)

Lemma in_splitT : forall (x : form) (l : list form), In x l ->
  {l1 & {l2 & l = l1 ++ x :: l2} }.
Proof.
induction l ; cbn ; intros ; [ contradiction |auto].
destruct (form_eq_dec a x) ; subst.
- exists [], l ; cbn ; auto.
- assert (In x l) by (destruct H ; auto ; contradiction).
  apply IHl in H0 as [l1 [l2 H0]] ; subst.
  exists (a :: l1), l2 ; cbn; auto.
Qed.

Lemma in_app_orT : forall (l m : list form) (a : form), In a (l ++ m) -> {In a l} + {In a m}.
Proof.
induction l ; cbn ; intros ; auto.
destruct (form_eq_dec a a0) ; subst.
- left ; auto.
- assert (In a0 (l ++ m)) by (destruct H ; auto ; contradiction).
  apply IHl in H0 as [H1 | H1] ; auto.
Qed.

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

(* The issue with lists is that we do not have
   exchange for free. If not set up properly,
   you can really end up in a nightmarish proof
   thousands of lines long (first hand experience
   speaking here...). *)

   (* We need a height-preserving version of exchange.
   The reason for this is that we prove some of
   our results by induction on the height of proofs,
   and in some intermediate steps we will need to
   rearrange our context to apply the adequate rule / 
   induction hypothesis. *)

Theorem exchange_hp Γ Γ' φ (Hp: Γ ⊢ φ) : Γ ≡ₚ Γ' ->
      {Hp' : Γ' ⊢ φ | height Hp' <= height Hp} .
Proof.
revert Γ'.
induction Hp ; subst ; intros Γ' Hper.
- assert (In (# p) Γ').
  { apply Permutation_in with (Γ0 ++ # p :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  pose (PId Γ2 Γ3 p). exists p0 ; cbn ; auto.
- assert (In ⊥ Γ').
  { apply Permutation_in with (Γ0 ++ ⊥ :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  pose (BotL Γ2 Γ3 φ). exists p ; cbn ; auto.
- destruct (IHHp1 _ Hper) as [Hp1' Hh1'] ; destruct (IHHp2 _ Hper) as [Hp2' Hh2'].
  pose (AndR _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
- assert (In (φ ∧ ψ) Γ').
  { apply Permutation_in with (Γ0 ++ (φ ∧ ψ) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  destruct (IHHp (Γ2 ++ φ :: ψ :: Γ3)) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle ; do 2 (apply Permutation_cons ; auto).
    apply Permutation_app_inv in Hper ; auto.
  + pose (AndL _ _ _ _ _ Hp'). exists p ; cbn ; lia.
- destruct (IHHp _ Hper) as [Hp' Hh'].
  pose (OrR1 _ _ ψ Hp'). exists p ; cbn ; lia.
- destruct (IHHp _ Hper) as [Hp' Hh'].
  pose (OrR2 _ φ _ Hp'). exists p ; cbn ; lia.
- assert (In (φ ∨ ψ) Γ').
  { apply Permutation_in with (Γ0 ++ (φ ∨ ψ) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  destruct (IHHp1 (Γ2 ++ φ :: Γ3)) as [Hp1' Hh1'].
  + repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
  + destruct (IHHp2 (Γ2 ++ ψ :: Γ3)) as [Hp2' Hh2'].
    * repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
      apply Permutation_app_inv in Hper ; auto.
    * pose (OrL _ _ _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
- destruct (IHHp (φ :: Γ')) as [Hp' Hh'].
  + apply Permutation_cons ; auto.
  + pose (ImpR _ _ _ Hp'). exists p ; cbn ; lia.
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
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc ; cbn.
    destruct (IHHp (Γ5 ++ φ :: Γ6 ++ # p :: Γ4)) as [Hp' Hh'].
    * repeat rewrite <- Permutation_middle.
      rewrite perm_swap. do 2 (apply Permutation_cons ; auto).
      repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
      repeat apply Permutation_cons_inv in Hper. rewrite <- app_assoc in Hper ; auto.
    * pose (ImpLVar2 _ _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc ; cbn.
    destruct (IHHp (Γ3 ++ # p :: Γ5 ++ φ :: Γ6)) as [Hp' Hh'].
    * repeat rewrite <- Permutation_middle.
      do 2 (apply Permutation_cons ; auto).
      repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
      repeat apply Permutation_cons_inv in Hper ; auto.
    * pose (ImpLVar1 _ _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
- assert (In (# p → φ) Γ').
  { apply Permutation_in with (Γ0 ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ3 [Γ4 H]] ; subst.
  assert (In (# p) (Γ3 ++ Γ4)).
  { assert (In (# p) (Γ3 ++ (# p → φ) :: Γ4)).
    apply Permutation_in with (Γ0 ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; [ auto | apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; split].
    apply in_or_app ; apply in_app_or in H as [H | H] ; auto. inversion H ; [ discriminate | auto]. }
  apply in_app_orT in H as [H | H].
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc ; cbn.
    destruct (IHHp (Γ5 ++ # p :: Γ6 ++ φ :: Γ4)) as [Hp' Hh'].
    * repeat rewrite <- Permutation_middle.
      rewrite perm_swap. do 2 (apply Permutation_cons ; auto).
      repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
      repeat apply Permutation_cons_inv in Hper. rewrite <- app_assoc in Hper ; auto.
    * pose (ImpLVar1 _ _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
  + apply in_splitT in H as [Γ5 [Γ6 H]] ; subst ; repeat rewrite <- app_assoc ; cbn.
    destruct (IHHp (Γ3 ++ φ :: Γ5 ++ # p :: Γ6)) as [Hp' Hh'].
    * repeat rewrite <- Permutation_middle.
      do 2 (apply Permutation_cons ; auto).
      repeat rewrite <- Permutation_middle in Hper ; cbn in Hper.
      repeat apply Permutation_cons_inv in Hper ; auto.
    * pose (ImpLVar2 _ _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
- assert (In (φ1 ∧ φ2 → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ (φ1 ∧ φ2 → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  destruct (IHHp (Γ2 ++ (φ1 → φ2 → φ3) :: Γ3)) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
  + pose (ImpLAnd _ _ _ _ _ _ Hp'). exists p ; cbn ; lia.
- assert (In (φ1 ∨ φ2 → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ (φ1 ∨ φ2 → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  destruct (IHHp (Γ2 ++ (φ1 → φ3) :: (φ2 → φ3) :: Γ3)) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
  + pose (ImpLOr _ _ _ _ _ _ Hp'). exists p ; cbn ; lia.
- assert (In ((φ1 → φ2) → φ3) Γ').
  { apply Permutation_in with (Γ0 ++ ((φ1 → φ2) → φ3) :: Γ1) ; [ auto | apply in_or_app ; right ; left ; split]. }
  apply in_splitT in H as [Γ2 [Γ3 H]] ; subst.
  destruct (IHHp1 (Γ2 ++ (φ2 → φ3) :: Γ3)) as [Hp1' Hh1'].
  + repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
    apply Permutation_app_inv in Hper ; auto.
  + destruct (IHHp2 (Γ2 ++ φ3 :: Γ3)) as [Hp2' Hh2'].
    * repeat rewrite <- Permutation_middle ; repeat apply Permutation_cons ; auto.
      apply Permutation_app_inv in Hper ; auto.
    * pose (ImpLImp _ _ _ _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
Qed.


Theorem exchange Γ Γ' φ : Γ ≡ₚ Γ' -> Γ ⊢ φ -> Γ' ⊢ φ.
Proof.
intros. destruct (exchange_hp _ _ _ H0 H) ; auto.
Qed.


(** ** Weakening *)

Theorem weakening_hp Γ φ (Hp: Γ ⊢ φ) ψ:
      {Hp' : ψ :: Γ ⊢ φ | height Hp' <= height Hp} .
Proof.
revert ψ. induction Hp ; intro ψ'.
- pose (PId (ψ' :: Γ0) Γ1 p) ; cbn in p0. exists p0 ; cbn ; lia.
- pose (BotL (ψ' :: Γ0) Γ1 φ) ; cbn in p. exists p ; cbn ; lia.
- destruct (IHHp1 ψ') as [Hp1' Hh1'] ; destruct (IHHp2 ψ') as [Hp2' Hh2'].
  pose (AndR _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (AndL (ψ' :: Γ0) _ _ _ _ Hp'). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (OrR1 _ _ ψ Hp'). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (OrR2 _ φ _ Hp'). exists p ; cbn ; lia.
- destruct (IHHp1 ψ') as [Hp1' Hh1'] ; destruct (IHHp2 ψ') as [Hp2' Hh2'].
  pose (OrL (ψ' :: Γ0) _ _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  destruct (exchange_hp _ (φ :: ψ' :: Γ) _ Hp') as [Hp'' Hh''].
  + apply perm_swap.
  + pose (ImpR _ _ _ Hp''). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (ImpLVar1 (ψ' :: Γ0) _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (ImpLVar2 (ψ' :: Γ0) _ _ _ _ _ Hp'). exists p0 ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (ImpLAnd (ψ' :: Γ0) _ _ _ _ _ Hp'). exists p ; cbn ; lia.
- destruct (IHHp ψ') as [Hp' Hh'].
  pose (ImpLOr (ψ' :: Γ0) _ _ _ _ _ Hp'). exists p ; cbn ; lia.
- destruct (IHHp1 ψ') as [Hp1' Hh1'] ; destruct (IHHp2 ψ') as [Hp2' Hh2'].
  pose (ImpLImp (ψ' :: Γ0) _ _ _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
Qed.

Theorem weakening  ψ Γ φ : Γ ⊢ φ -> ψ :: Γ ⊢ φ.
Proof.
intro Hp. destruct (weakening_hp Γ φ Hp ψ) ; auto.
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
assert(Hle : weight φ <= w) by lia.
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

(* We can also prove that invertibility of some rules are hp. *)

Lemma AndL_rev_hp Γ φ ψ θ (Hp : (φ ∧ ψ) :: Γ ⊢ θ) :
      { Hp' : φ :: ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
remember ((φ ∧ ψ) :: Γ) as Γ' eqn:HH'.
assert (HH : Γ' ≡ₚ (φ ∧ ψ) :: Γ) by (rewrite HH' ; auto).
clear HH'.
revert φ ψ Γ HH.
induction Hp; intros φ0 ψ0 Γ' Heq ; auto with proof.
- (* As # p is hidden in Γ', we use in_Permutation to make it 
     explicit. So, we need to explicitly prove that it is in Γ'. *)
  assert (In (# p) Γ').
  { assert (In (# p) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  (* Then we can apply our lemma to exhibit # p. *)
  apply in_Permutation in H as [Γ'' H].
  (* We create the following leaf-proof. *)
  pose (PId [φ0 ; ψ0] Γ'' p).
  (* At this point we know that our context is a permutation
     of the context given in p0. *)
  destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p0).
  + cbn ; do 2 (apply Permutation_cons ; auto).
  + exists x ; cbn in * ; auto.
- assert (In ⊥ Γ').
  { assert (In ⊥ ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  pose (BotL [φ0 ; ψ0] Γ'' φ).
  destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
  + cbn ; do 2 (apply Permutation_cons ; auto).
  + exists x ; cbn in * ; auto.
- destruct (IHHp1 _ _ _ Heq) as [Hp1' Hh1'] ; destruct (IHHp2 _ _ _ Heq) as [Hp2' Hh2'].
  pose (AndR _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
(* the main case *)
- (* Here we do not know whether (φ ∧ ψ) is the same conjunction 
     as (φ0 ∧ ψ0). So, we make a case distinction. *)
  case (decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0. 
  (* If they are the same *)
  + inversion Heq0 ; subst.
    destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ Hp).
    * repeat rewrite <- Permutation_middle ; do 2 (apply Permutation_cons ; auto).
      assert (Heqp : Γ0 ++ (φ0 ∧ ψ0) :: Γ1 ≡ₚ (φ0 ∧ ψ0) :: Γ') by (rewrite Heq ; auto).
      repeat rewrite <- Permutation_middle in Heqp ; apply Permutation_cons_inv in Heqp ; auto.
    * exists x ; cbn ; lia.
  (* If they are not *)
  + assert (In (φ ∧ ψ) Γ').
    { assert (In (φ ∧ ψ) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
      inversion H ; auto. exfalso ; auto. }
    apply in_Permutation in H as [Γ'' H].
    destruct (IHHp φ0 ψ0 (φ :: ψ :: Γ'')) as [Hp' Hh'].
    * repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
      do 2 (apply Permutation_cons ; auto). rewrite <- H in Heq.
      rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
      apply Permutation_cons_inv in Heq ; auto.
    * pose (AndL [φ0 ; ψ0] Γ'' _ _ _ Hp').
       destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
       -- rewrite H ; auto.
       -- exists x ; cbn in * ; lia.
- destruct (IHHp _ _ _ Heq) as [Hp' Hh'].
  pose (OrR1 _ _ ψ Hp'). exists p ; cbn ; lia.
- destruct (IHHp _ _ _ Heq) as [Hp' Hh'].
  pose (OrR2 _ φ _ Hp'). exists p ; cbn ; lia.
- assert (In (φ ∨ ψ) Γ').
  { assert (In (φ ∨ ψ) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  destruct (IHHp1 φ0 ψ0 (φ :: Γ'')) as [Hp1' Hh1'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    apply Permutation_cons ; auto. rewrite <- H in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + destruct (IHHp2 φ0 ψ0 (ψ :: Γ'')) as [Hp2' Hh2'].
    * repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
      apply Permutation_cons ; auto. rewrite <- H in Heq.
      rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
      apply Permutation_cons_inv in Heq ; auto.
    * pose (OrL [φ0 ; ψ0] Γ'' _ _ _ Hp1' Hp2').
      destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
      -- rewrite H ; auto.
      -- exists x ; cbn in * ; lia.
- destruct (IHHp φ0 ψ0 (φ :: Γ')) as [Hp' Hh'].
  + rewrite perm_swap ; apply Permutation_cons ; auto.
  + destruct (exchange_hp _ (φ :: φ0 :: ψ0 :: Γ') _ Hp').
    * repeat rewrite (perm_swap φ0) ; apply Permutation_cons ; auto.
      apply perm_swap.
    * pose (ImpR _ _ _ x). exists p ; cbn ; lia.
- assert (In (# p) Γ').
  { assert (In (# p) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  assert (In (# p → φ) Γ'').
  { assert (In (# p → φ) ((φ0 ∧ ψ0) :: # p :: Γ'')) by (rewrite H ; rewrite <- Heq ; apply in_or_app ; right ; cbn ; right ; 
    apply in_or_app ; right ; cbn ; left ; auto).
    inversion H0 ; try discriminate. inversion H1 ; auto ; discriminate. }
  apply in_Permutation in H0 as [Γ''' H0].
  destruct (IHHp φ0 ψ0 (# p :: φ :: Γ''')) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    do 2 (apply Permutation_cons ; auto). rewrite <- H in Heq. rewrite <- H0 in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq. rewrite perm_swap in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + pose (ImpLVar1 [φ0 ; ψ0] [] Γ''' _ _ _ Hp').
    destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p0).
    -- cbn. rewrite H0 ; rewrite H ; auto.
    -- exists x ; cbn in * ; lia.
- assert (In (# p → φ) Γ').
  { assert (In (# p → φ) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  assert (In (# p) Γ'').
  { assert (In (# p) ((φ0 ∧ ψ0) :: (# p → φ) :: Γ'')) by (rewrite H ; rewrite <- Heq ; apply in_or_app ; right ; cbn ; right ; 
    apply in_or_app ; right ; cbn ; left ; auto).
    inversion H0 ; try discriminate. inversion H1 ; auto ; discriminate. }
  apply in_Permutation in H0 as [Γ''' H0].
  destruct (IHHp φ0 ψ0 (φ :: # p :: Γ''')) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    do 2 (apply Permutation_cons ; auto). rewrite <- H in Heq. rewrite <- H0 in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq. rewrite perm_swap in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + pose (ImpLVar2 [φ0 ; ψ0] [] Γ''' _ _ _ Hp').
    destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p0).
    -- cbn. rewrite H0 ; rewrite H ; auto.
    -- exists x ; cbn in * ; lia.
- assert (In (φ1 ∧ φ2 → φ3) Γ').
  { assert (In (φ1 ∧ φ2 → φ3) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  destruct (IHHp φ0 ψ0 ((φ1 → φ2 → φ3) :: Γ'')) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    apply Permutation_cons ; auto. rewrite <- H in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + pose (ImpLAnd [φ0 ; ψ0] Γ'' _ _ _ _ Hp').
    destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
    -- cbn. rewrite H ; auto.
    -- exists x ; cbn in * ; lia.
- assert (In (φ1 ∨ φ2 → φ3) Γ').
  { assert (In (φ1 ∨ φ2 → φ3) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  destruct (IHHp φ0 ψ0 ((φ1 → φ3) :: (φ2 → φ3) :: Γ'')) as [Hp' Hh'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    do 2 (apply Permutation_cons ; auto). rewrite <- H in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + pose (ImpLOr [φ0 ; ψ0] Γ'' _ _ _ _ Hp').
    destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
    -- cbn. rewrite H ; auto.
    -- exists x ; cbn in * ; lia.
- assert (In ((φ1 → φ2) → φ3) Γ').
  { assert (In ((φ1 → φ2) → φ3) ((φ0 ∧ ψ0) :: Γ')) by (rewrite <- Heq ; apply in_or_app ; right ; cbn ; left ; auto).
    inversion H ; auto ; discriminate. }
  apply in_Permutation in H as [Γ'' H].
  destruct (IHHp1 φ0 ψ0 ((φ2 → φ3) :: Γ'')) as [Hp1' Hh1'].
  + repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
    apply Permutation_cons ; auto. rewrite <- H in Heq.
    rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
    apply Permutation_cons_inv in Heq ; auto.
  + destruct (IHHp2 φ0 ψ0 (φ3 :: Γ'')) as [Hp2' Hh2'].
    * repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ0 ∧ ψ0)).
      apply Permutation_cons ; auto. rewrite <- H in Heq.
      rewrite perm_swap in Heq. repeat rewrite <- Permutation_middle in Heq.
      apply Permutation_cons_inv in Heq ; auto.
    * pose (ImpLImp [φ0 ; ψ0] Γ'' _ _ _ _ Hp1' Hp2').
      destruct (exchange_hp _ (φ0 :: ψ0 :: Γ') _ p).
      -- cbn. rewrite H ; auto.
      -- exists x ; cbn in * ; lia.
Qed.

Lemma AndL_rev  Γ φ ψ θ: (φ ∧ ψ) :: Γ ⊢ θ -> φ :: ψ :: Γ ⊢ θ.
Proof.
intro Hp. destruct (AndL_rev_hp Γ φ ψ θ Hp) as [Hp' Hh'] ; auto.
Admitted.

Lemma OrL_rev_hp  Γ φ ψ θ (Hp : (φ ∨ ψ) :: Γ ⊢ θ) :
      { Hp' : φ :: Γ ⊢ θ | height Hp' <= height Hp} *
      { Hp' : ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma OrL_rev  Γ φ ψ θ: (φ ∨ ψ) :: Γ ⊢ θ  → (φ :: Γ ⊢ θ) * (ψ :: Γ ⊢ θ).
Proof.
intro Hp. destruct (OrL_rev_hp Γ φ ψ θ Hp) as [[Hp1 Hh1] [Hp2 Hh2]]; auto.
Qed.


Lemma TopL_rev Γ θ : ⊤ :: Γ ⊢ θ -> Γ ⊢ θ.
Proof.
Admitted.

Local Hint Immediate TopL_rev : proof.

Lemma ImpLVar_rev_hp Γ p φ ψ (Hp : (# p → φ) :: Γ ⊢ ψ) :
      { Hp' : φ :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLVar_rev  Γ p φ ψ: (# p → φ) :: Γ ⊢ ψ  → φ :: Γ ⊢ ψ.
Proof.
Admitted.

Lemma ImpLImp_rev_hp Γ φ1 φ2 φ3 ψ (Hp : ((φ1 → φ2) → φ3) :: Γ ⊢ ψ) :
      { Hp' : φ3 :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLImp_prev  Γ φ1 φ2 φ3 ψ: ((φ1 → φ2) → φ3) :: Γ ⊢ ψ -> φ3 :: Γ ⊢ ψ.
Proof.
intro Hp. destruct (ImpLImp_rev_hp Γ φ1 φ2 φ3 ψ Hp) ; auto.
Qed.

Lemma ImpLOr_rev_hp Γ φ1 φ2 φ3 ψ (Hp : (φ1 ∨ φ2 → φ3) :: Γ ⊢ ψ) :
      { Hp' : (φ1 → φ3) :: (φ2 → φ3) :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLOr_rev  Γ φ1 φ2 φ3 ψ:
  ((φ1 ∨ φ2) → φ3) :: Γ ⊢ ψ -> (φ1 → φ3) :: (φ2 → φ3) :: Γ ⊢ ψ.
Proof.
intro Hp. destruct (ImpLOr_rev_hp Γ φ1 φ2 φ3 ψ Hp) ; auto.
Qed.

Lemma ImpLAnd_rev_hp Γ φ1 φ2 φ3 ψ (Hp : (φ1 ∧ φ2 → φ3) :: Γ ⊢ ψ) :
      { Hp' : (φ1 → φ2 → φ3) :: Γ ⊢ ψ | height Hp' <= height Hp}.
Proof.
Admitted.

Lemma ImpLAnd_rev  Γ φ1 φ2 φ3 ψ: (φ1 ∧ φ2 → φ3) :: Γ ⊢ ψ ->  (φ1 → φ2 → φ3) :: Γ ⊢ ψ .
Proof.
intro Hp. destruct (ImpLAnd_rev_hp Γ φ1 φ2 φ3 ψ Hp) ; auto.
Qed.


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
  eapply exchange ; [ | apply ImpLVar_rev with p ; eapply exchange ; [ | exact Hp']].
  + repeat rewrite <- Permutation_middle.
    transitivity (φ :: ψ0 :: # p :: Γ0 ++ Γ1 ++ Γ2).
    * apply Permutation_cons ; reflexivity.
    * repeat rewrite (perm_swap φ) ; apply Permutation_cons ; auto.
  + repeat rewrite <- Permutation_middle.
    repeat rewrite (perm_swap ψ0) ; apply Permutation_cons ; auto. apply perm_swap.
- apply exchange with (((ψ → ψ0) :: Γ0) ++ (# p → φ) :: Γ1 ++ # p :: Γ2) ; auto.
  apply ImpLVar2 ; cbn ; auto. apply IHHp.
  eapply exchange ; [ | apply ImpLVar_rev with p ; eapply exchange ; [ | exact Hp']].
  + repeat rewrite <- Permutation_middle.
    transitivity (φ :: ψ0 :: # p :: Γ0 ++ Γ1 ++ Γ2).
    * apply Permutation_cons ; reflexivity.
    * repeat rewrite (perm_swap φ) ; apply Permutation_cons ; auto.
  + repeat rewrite <- Permutation_middle.
    repeat rewrite (perm_swap ψ0) ; apply Permutation_cons ; auto.
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

Lemma ImpL_rev : forall φ Γ ψ θ, (φ → ψ) :: Γ ⊢ θ -> ψ :: Γ ⊢ θ.
Proof.
(* We need to manage a bit our goal so that we can
   more freely use permutations / exchange. *)
enough (forall Γ' θ, Γ' ⊢G4ip θ -> forall φ Γ ψ, Γ' ≡ₚ (φ → ψ) :: Γ -> ψ :: Γ ⊢ θ).
- intros. apply (H _ _ H0 φ Γ ψ) ; auto. 
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
    * eapply exchange.
      -- rewrite <- p0 ; reflexivity.
      -- apply (PId [ψ]) ; auto.
  + destruct (in_Permutation Γ' ⊥).
    * assert (In ⊥ ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * eapply exchange.
      -- rewrite <- p ; reflexivity.
      -- apply (BotL [ψ]) ; auto.
  + apply AndR.
    * apply IHHp1 ; auto.
    * apply IHHp2 ; auto.
  + destruct (in_Permutation Γ' (φ0 ∧ ψ0)).
    * assert (In (φ0 ∧ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * eapply exchange. 
      -- rewrite <- p ; reflexivity.
      -- apply (AndL [ψ]). apply IHHp. rewrite <- p in HH.
         repeat rewrite <- Permutation_middle.
         repeat rewrite (perm_swap φ0) ; apply Permutation_cons ; auto.
         rewrite (perm_swap ψ0) ; apply Permutation_cons ; auto.
         repeat rewrite <- Permutation_middle in HH.
         rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + apply OrR1 ; auto. 
  + apply OrR2 ; auto. 
  + destruct (in_Permutation Γ' (φ0 ∨ ψ0)).
    * assert (In (φ0 ∨ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * eapply exchange.
      -- rewrite <- p. reflexivity.
      -- apply (OrL [ψ]).
        ++ apply IHHp1. repeat rewrite <- Permutation_middle.
           rewrite perm_swap ; apply Permutation_cons ; auto.
           repeat rewrite <- Permutation_middle in HH. rewrite <- p in HH.
           rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
        ++ apply IHHp2. repeat rewrite <- Permutation_middle.
           rewrite perm_swap ; apply Permutation_cons ; auto.
           repeat rewrite <- Permutation_middle in HH. rewrite <- p in HH.
           rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + apply ImpR. eapply exchange.
    * apply perm_swap.
    * apply IHHp. rewrite perm_swap ; apply Permutation_cons ; auto. 
  + case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply exchange with (Γ0 ++ # p :: Γ1 ++ ψ :: Γ2) ; auto.
      repeat rewrite <- Permutation_middle ; rewrite perm_swap ; apply Permutation_cons ; auto.
      repeat rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
    * destruct (in_Permutation Γ' (# p → φ0)).
      -- assert (In (# p → φ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; auto).
         inversion H ; [ exfalso ; auto | auto].
      -- rewrite <- p0 in HH. destruct (in_Permutation x (# p)).
        ++ assert (In (# p) ((φ → ψ) :: (# p → φ0) :: x)) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
           inversion H ; [ discriminate | ]. inversion H0 ; [ discriminate | auto].
        ++ rewrite <- p1 in HH,p0.
           eapply exchange with (ψ :: (# p → φ0) :: # p :: x0) ; [ apply Permutation_cons ; auto | ].
           apply (ImpLVar2 [ψ] []).
           apply IHHp ; cbn.
           repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap (#p)) ; apply Permutation_cons ; auto.
           rewrite perm_swap ; apply Permutation_cons ; auto.
           repeat rewrite <- Permutation_middle in HH. repeat rewrite (perm_swap (#p)) in HH ; apply Permutation_cons_inv in HH ; auto.
           rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply exchange with (Γ0 ++ ψ :: Γ1 ++ # p :: Γ2) ; auto.
      repeat rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
      repeat rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
    * destruct (in_Permutation Γ' (# p → φ0)).
      -- assert (In (# p → φ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
         inversion H ; [ exfalso ; auto | auto].
      -- rewrite <- p0 in HH. destruct (in_Permutation x (# p)).
        ++ assert (In (# p) ((φ → ψ) :: (# p → φ0) :: x)) by (rewrite <- HH ; apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; auto).
           inversion H ; [ discriminate | ]. inversion H0 ; [ discriminate | auto].
        ++ rewrite <- p1 in HH,p0.
           eapply exchange with (ψ :: (# p → φ0) :: # p :: x0) ; [ apply Permutation_cons ; auto | ].
           apply (ImpLVar2 [ψ] []).
           apply IHHp ; cbn.
           repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap (#p)) ; apply Permutation_cons ; auto.
           rewrite perm_swap ; apply Permutation_cons ; auto.
           repeat rewrite <- Permutation_middle in HH. repeat rewrite (perm_swap (#p)) in HH ; apply Permutation_cons_inv in HH ; auto.
           rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + case (decide ((φ1 ∧ φ2 → φ3) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply exchange with (ψ :: Γ0 ++ Γ1).
      -- apply Permutation_cons ; auto.
         rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
      -- apply IHw with ((φ2 → ψ) :: Γ0 ++ Γ1) φ2 ; [ cbn in * ; lia | auto | ].
         apply IHw with ((φ1 → φ2 → ψ) :: Γ0 ++ Γ1) φ1 ; [ cbn in * ; lia | auto | ].
         apply exchange with (Γ0 ++ (φ1 → φ2 → ψ) :: Γ1) ; auto. rewrite Permutation_middle ; auto.
    * assert (In (φ1 ∧ φ2 → φ3) (Γ')).
      { assert (In (φ1 ∧ φ2 → φ3) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
        inversion H ; auto ; exfalso ; auto. }
      destruct (in_Permutation _ _ H) as [Γ'' Heq'].
      eapply exchange ; [ rewrite <- Heq' ; reflexivity | ].
      apply (ImpLAnd [ψ]). apply IHHp.
      rewrite perm_swap ; rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
      rewrite <- Heq' in HH ; rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + case (decide ((φ1 ∨ φ2 → φ3) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply contraction.
      apply IHw with (ψ :: (φ2 → ψ) :: Γ') φ2 ; [ cbn in * ; lia | apply perm_swap | ].
      apply IHw with ((φ1 → ψ) :: (φ2 → ψ) :: Γ') φ1 ; [ cbn in * ; lia | auto | ].
      apply exchange with (Γ0 ++ (φ1 → ψ) :: (φ2 → ψ) :: Γ1) ; auto.
      do 2 (rewrite <- Permutation_middle ; apply Permutation_cons ; auto).
      rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
    * assert (In (φ1 ∨ φ2 → φ3) (Γ')).
      { assert (In (φ1 ∨ φ2 → φ3) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
        inversion H ; auto ; exfalso ; auto. }
      destruct (in_Permutation _ _ H) as [Γ'' Heq'].
      eapply exchange ; [ rewrite <- Heq' ; reflexivity | ].
      apply (ImpLOr [ψ]). apply IHHp.
      repeat rewrite <- (perm_swap (φ → ψ)) ; repeat rewrite <- Permutation_middle ; do 2 (apply Permutation_cons ; auto).
      rewrite <- Heq' in HH ; rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      apply exchange with (Γ0 ++ ψ :: Γ1) ; auto.
      rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
      rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
    * assert (In ((φ1 → φ2) → φ3) (Γ')).
      { assert (In ((φ1 → φ2) → φ3) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
        inversion H ; auto ; exfalso ; auto. }
      destruct (in_Permutation _ _ H) as [Γ'' Heq'].
      eapply exchange ; [ rewrite <- Heq' ; reflexivity | ].
      apply (ImpLImp [ψ]).
      -- apply IHHp1. repeat rewrite <- (perm_swap (φ → ψ)) ; repeat rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
         rewrite <- Heq' in HH ; rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
      -- apply IHHp2. repeat rewrite <- (perm_swap (φ → ψ)) ; repeat rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
         rewrite <- Heq' in HH ; rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
Qed.

Global Hint Resolve ImpL_rev : proof.

Lemma OrR_idemp  Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp ; auto with proof. Qed.

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
