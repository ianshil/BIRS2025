(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Cut.v *)


(** * Cut Admissibility *)
Require Import syntax list_sequent list_sequent_props. 
Require Import Coq.Program.Equality.
Require Import Arith Lia.

Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> φ :: Γ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
(* Primary induction on the weight of the cut formula. *)
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
(* Secondary induction on the sum of the heights of the 
   premises of the cut. *)
intros Hp1 Hp2.
remember (height Hp1 + height Hp2) as h.
revert h ψ Γ Hp1 Hp2 Heqh.
refine  (@well_founded_induction _ _ Nat.lt_wf_0 _ _).
intros h. intro IHh. intros ψ Γ Hp1 Hp2 Heqh.
(* We inspect the structure of the proof of the left 
   premise "Γ ⊢G4ip φ". *)
destruct Hp1; simpl in Hw,Heqh.
- eapply exchange ; [ apply Permutation_middle | ].
  apply contraction. eapply exchange ; [ | exact Hp2].
  rewrite <- Permutation_middle ; auto.
- apply BotL.
- pose (AndL_rev _ _ _ _ Hp2). do 2 apply IHw in p ; auto ; try lia. 
  all: apply weakening; assumption.
- apply AndL. destruct (exchange_hp _ ((φ ∧ ψ0) :: θ :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
  + rewrite <- Permutation_middle. apply perm_swap.
  + destruct (AndL_rev_hp _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (θ :: Γ0 ++ φ :: ψ0 :: Γ1) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle.
      rewrite (perm_swap _ θ) ; apply Permutation_cons ; auto. apply perm_swap.
    * apply IHh with (Hp1 := Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ lia | auto ].
- destruct (OrL_rev _ _ _ _ Hp2). apply (IHw φ); [lia| |]; tauto.
- destruct (OrL_rev _ _ _ _ Hp2). apply (IHw ψ0); [lia| |] ; tauto.
- apply OrL.
  + destruct (exchange_hp _ ((φ ∨ ψ0) :: θ :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
    * rewrite <- Permutation_middle ; apply perm_swap.
    * destruct (OrL_rev_hp _ _ _ _ Hp2') as [[Hp3 Hh3] [Hp4 Hh4]].
      destruct (exchange_hp _ (θ :: Γ0 ++ φ :: Γ1) _ Hp3) as [Hp3' Hh3'].
      -- rewrite <- Permutation_middle ; apply perm_swap.
      -- apply IHh with (Hp1 := Hp1_1) (Hp2 := Hp3') (y:= height Hp1_1 + height Hp3') ; [ lia | auto ].
  + destruct (exchange_hp _ ((φ ∨ ψ0) :: θ :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
    * rewrite <- Permutation_middle ; apply perm_swap.
    * destruct (OrL_rev_hp _ _ _ _ Hp2') as [[Hp3 Hh3] [Hp4 Hh4]].
      destruct (exchange_hp _ (θ :: Γ0 ++ ψ0 :: Γ1) _ Hp4) as [Hp4' Hh4'].
      -- rewrite <- Permutation_middle ; apply perm_swap.
      -- apply IHh with (Hp1 := Hp1_2) (Hp2 := Hp4') (y:= height Hp1_2 + height Hp4') ; [ lia | auto ].
- (* (V) *)
  (* The last rule applied was ImpR, so the cut
     formula is an implication. Here, we need to
     inspect the structure of the proof of the
     other premise. *)
  remember ((φ → ψ0) :: Γ) as Γ'.
  destruct Hp2 ; subst ; cbn in IHh.
  + assert (In (#p) Γ).
    { assert (In # p ((φ → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
      inversion H ; [discriminate | auto]. }
    apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst. apply PId.
  + assert (In ⊥ Γ).
    { assert (In ⊥ ((φ → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
      inversion H ; [discriminate | auto]. }
    apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst. apply BotL.
  + pose (ImpR _ _ _ Hp1). apply AndR.
     * apply IHh with (Hp1 := p) (Hp2 := Hp2_1) (y:= height p + height Hp2_1) ; [ cbn ; lia | auto ].
     * apply IHh with (Hp1 := p) (Hp2 := Hp2_2) (y:= height p + height Hp2_2) ; [ cbn ; lia | auto ].
  + assert (In (φ0 ∧ ψ) Γ).
    { assert (In (φ0 ∧ ψ) ((φ → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
      inversion H ; [discriminate | auto]. }
    apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst.
    apply AndL. pose (ImpR _ _ _ Hp1).
    destruct (exchange_hp _ ((φ0 ∧ ψ) :: Γ' ++ Γ'') _ p) as [p' Hh'].
    * rewrite Permutation_middle ; auto.
    * destruct (AndL_rev_hp _ _ _ _ p') as [p'' Hh''].
      destruct (exchange_hp _ (Γ' ++ φ0 :: ψ :: Γ'') _ p'') as [p3 Hh3].
      -- repeat rewrite <- Permutation_middle ; auto.
      -- destruct (exchange_hp _ ((φ → ψ0) :: Γ' ++ φ0 :: ψ :: Γ'') _ Hp2) as [Hp2' Hh2'].
         ++ repeat rewrite <- Permutation_middle.
            do 2 (rewrite <- (perm_swap (φ → ψ0)) ; apply Permutation_cons ; auto).
           pose (Permutation_app_inv Γ0 Γ1 ((φ → ψ0) :: Γ') Γ'' (φ0 ∧ ψ)). 
           cbn in p0. apply p0 ; rewrite HeqΓ' ; auto.
         ++ apply IHh with (Hp1 := p3) (Hp2 := Hp2') (y:= height p3 + height Hp2') ; [ cbn in * ; lia | auto ].
  + apply OrR1. pose (ImpR _ _ _ Hp1).
    apply IHh with (Hp1 := p) (Hp2 := Hp2) (y:= height p + height Hp2) ; [ cbn ; lia | auto ].
  + apply OrR2. pose (ImpR _ _ _ Hp1).
    apply IHh with (Hp1 := p) (Hp2 := Hp2) (y:= height p + height Hp2) ; [ cbn ; lia | auto ].
  + pose (ImpR _ _ _ Hp1).
    assert (In (φ0 ∨ ψ) Γ).
    { assert (In (φ0 ∨ ψ) ((φ → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
      inversion H ; [discriminate | auto]. }
    apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst.
    apply OrL.
    * destruct (exchange_hp _ ((φ0 ∨ ψ) :: Γ' ++ Γ'') _ p) as [p' Hh'].
      -- rewrite Permutation_middle ; auto.
      -- destruct (OrL_rev_hp _ _ _ _ p') as [[pl Hlh] [pr Hrh]].
         destruct (exchange_hp _ (Γ' ++ φ0 :: Γ'') _ pl) as [p3 Hh3].
         ++ rewrite <- Permutation_middle ; auto.
         ++ destruct (exchange_hp _ ((φ → ψ0) :: Γ' ++ φ0 :: Γ'') _ Hp2_1) as [Hp2_1' Hh2_1'].
            ** repeat rewrite <- Permutation_middle.
               rewrite <- (perm_swap (φ → ψ0)) ; apply Permutation_cons ; auto.
               pose (Permutation_app_inv Γ0 Γ1 ((φ → ψ0) :: Γ') Γ'' (φ0 ∨ ψ)). 
               cbn in p0. apply p0 ; rewrite HeqΓ' ; auto.
            ** apply IHh with (Hp1 := p3) (Hp2 := Hp2_1') (y:= height p3 + height Hp2_1') ; [ cbn in * ; lia | auto ].
    * destruct (exchange_hp _ ((φ0 ∨ ψ) :: Γ' ++ Γ'') _ p) as [p' Hh'].
      -- rewrite Permutation_middle ; auto.
      -- destruct (OrL_rev_hp _ _ _ _ p') as [[pl Hlh] [pr Hrh]].
         destruct (exchange_hp _ (Γ' ++ ψ :: Γ'') _ pr) as [p3 Hh3].
         ++ rewrite <- Permutation_middle ; auto.
         ++ destruct (exchange_hp _ ((φ → ψ0) :: Γ' ++ ψ :: Γ'') _ Hp2_2) as [Hp2_2' Hh2_2'].
            ** repeat rewrite <- Permutation_middle.
               rewrite <- (perm_swap (φ → ψ0)) ; apply Permutation_cons ; auto.
               pose (Permutation_app_inv Γ0 Γ1 ((φ → ψ0) :: Γ') Γ'' (φ0 ∨ ψ)). 
               cbn in p0. apply p0 ; rewrite HeqΓ' ; auto.
            ** apply IHh with (Hp1 := p3) (Hp2 := Hp2_2') (y:= height p3 + height Hp2_2') ; [ cbn in * ; lia | auto ].
  + apply ImpR. pose (ImpR _ _ _ Hp1).
    destruct (weakening_hp _ _ p φ0).
    destruct (exchange_hp _ ((φ → ψ0) :: φ0 :: Γ) _ Hp2) as [Hp2' Hh2'].
    * apply perm_swap.
    * apply IHh with (Hp1 := x) (Hp2 := Hp2') (y:= height x + height Hp2') ; [ cbn in * ; lia | auto ].
  (* The remaining subcases are implication left rule, which may have
     the cut formula as principal formula. So, in each subcase we check
     whether the principal formula is the cut formula. *)
  + case (decide ((#p → φ0) = (φ → ψ0))).
      (* If the cut formula is principal *)
      * intro Heq'; dependent destruction Heq'.
        apply (IHw ψ0) ; auto.
        -- lia.
        -- assert (In (#p) Γ).
           { assert (In (#p) ((#p → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
             inversion H ; [discriminate | auto]. }
           apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst.
           apply exchange with (# p :: Γ' ++ Γ'') ; [ apply Permutation_middle | ].
           apply contraction.
           apply exchange with (# p :: Γ' ++ # p :: Γ'') ; [ repeat rewrite <- Permutation_middle ; auto | auto].
        -- apply exchange with (Γ0 ++ # p :: Γ1 ++ ψ0 :: Γ2) ; [ | auto].
           rewrite Permutation_middle. rewrite perm_swap. do 2 (rewrite <- Permutation_middle).
           apply Permutation_cons ; auto.
           symmetry. apply Permutation_cons_app_inv with (# p → ψ0). rewrite <- HeqΓ'.
           repeat rewrite <- Permutation_middle. apply perm_swap.
      (* If the cut formula is not principal *)
      * intro Hneq. admit.
  + case (decide ((#p → φ0) = (φ → ψ0))).
      (* If the cut formula is principal *)
      * intro Heq'; dependent destruction Heq'.
        apply (IHw ψ0) ; auto.
        -- lia.
        -- assert (In (#p) Γ).
           { assert (In (#p) ((#p → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; right ;
             apply in_or_app ; right ; left ; split).
             inversion H ; [discriminate | auto]. }
           apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst.
           apply exchange with (# p :: Γ' ++ Γ'') ; [ apply Permutation_middle | ].
           apply contraction.
           apply exchange with (# p :: Γ' ++ # p :: Γ'') ; [ repeat rewrite <- Permutation_middle ; auto | auto].
        -- apply exchange with (Γ0 ++ ψ0 :: Γ1 ++ # p :: Γ2) ; [ | auto].
           rewrite <- Permutation_middle. apply Permutation_cons ; auto.
           symmetry. apply Permutation_cons_app_inv with (# p → ψ0) ; rewrite HeqΓ' ; auto.
      (* If the cut formula is not principal *)
      * intro Hneq. admit.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * admit.
      * admit.
  + case (decide (((φ1 ∨ φ2) → φ3)= (φ → ψ0))).
      * admit.
      * admit.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ0))).
     * admit.
     * (* (V-d) *) admit.
- apply ImpLVar1. 
  destruct (exchange_hp _ ((# p → φ) :: ψ0 :: Γ0 ++ # p :: Γ1 ++ Γ2) _ Hp2) as [Hp2' Hh2'].
  + repeat rewrite <- Permutation_middle.
    do 2 (rewrite <- (perm_swap (# p → φ)) ; apply Permutation_cons ; auto).
  + destruct (imp_cut_hp _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ # p :: Γ1 ++ φ :: Γ2) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle.
      do 2 (rewrite <- (perm_swap (φ)) ; apply Permutation_cons ; auto).
    * apply IHh with (Hp1 :=Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ cbn in * ; lia | auto ].
- apply ImpLVar2. 
  destruct (exchange_hp _ ((# p → φ) :: ψ0 :: Γ0 ++ Γ1 ++ # p :: Γ2) _ Hp2) as [Hp2' Hh2'].
  + repeat rewrite <- Permutation_middle.
    rewrite <- (perm_swap (# p → φ) ψ0) ; apply Permutation_cons ; auto.
  + destruct (imp_cut_hp _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ φ :: Γ1 ++ # p :: Γ2) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle.
      rewrite <- (perm_swap φ ψ0) ; apply Permutation_cons ; auto.
    * apply IHh with (Hp1 :=Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ cbn in * ; lia | auto ].
- apply ImpLAnd.
  destruct (exchange_hp _ ((φ1 ∧ φ2 → φ3) :: ψ0 :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
  + rewrite perm_swap. apply Permutation_cons ; auto. rewrite Permutation_middle ; auto.
  + destruct (ImpLAnd_rev_hp _ _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ (φ1 → φ2 → φ3) :: Γ1) _ Hp3) as [Hp3' Hh3'].
    * rewrite perm_swap. apply Permutation_cons ; auto. apply Permutation_middle.
    * apply IHh with (Hp1 :=Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ cbn in * ; lia | auto ].
- apply ImpLOr.
  destruct (exchange_hp _ ((φ1 ∨ φ2 → φ3) :: ψ0 :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
  + rewrite perm_swap. apply Permutation_cons ; auto. rewrite Permutation_middle ; auto.
  + destruct (ImpLOr_rev_hp _ _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ (φ1 → φ3) :: (φ2 → φ3) :: Γ1) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap ψ0). apply Permutation_cons ; auto.
    * apply IHh with (Hp1 :=Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ cbn in * ; lia | auto ].
- apply ImpLImp ; auto.
  destruct (exchange_hp _ (((φ1 → φ2) → φ3) :: ψ0 :: Γ0 ++ Γ1) _ Hp2) as [Hp2' Hh2'].
  + rewrite perm_swap. apply Permutation_cons ; auto. rewrite Permutation_middle ; auto.
  + destruct (ImpLImp_rev_hp _ _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ φ3 :: Γ1) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap ψ0) ; auto.
    * apply IHh with (Hp1 :=Hp1_2) (Hp2 := Hp3') (y:= height Hp1_2 + height Hp3') ; [ cbn in * ; lia | auto ].
Admitted.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> φ :: Γ' ⊢ ψ ->
  Γ ++ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- apply exchange with (Γ ++ φ :: Γ') ; [ rewrite Permutation_middle ; auto | ].
  apply generalised_weakeningL, π2.
Qed.