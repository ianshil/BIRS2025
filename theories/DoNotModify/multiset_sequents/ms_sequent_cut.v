(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Cut.v *)


(** * Cut Admissibility *)
Require Import syntax ms_sequent ms_sequent_props. 
Require Import ms_order.
Require Import Coq.Program.Equality.


Local Hint Rewrite @elements_env_add : order.


Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
remember (Γ, ψ) as pe.
replace Γ with pe.1 by now subst.
replace ψ with pe.2 by now subst. clear Heqpe Γ ψ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_env_ms_order _ _).
intros (Γ &ψ). simpl. intro IHW'. assert (IHW := fun Γ0 => fun ψ0 => IHW' (Γ0, ψ0)).
simpl in IHW. clear IHW'. intros HPφ HPψ.
Ltac otac Heq := subst; repeat rewrite env_replace in Heq by trivial; repeat rewrite env_add_remove by trivial; order_tac; rewrite Heq; order_tac.
destruct HPφ; simpl in Hw.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW; auto with proof. otac Heq.
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW; auto with proof.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
- (* (V) *) (* hard:  *)
(* START *)
  remember (Γ • (φ → ψ0)) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ φ → ψ0]}) by ms.
  assert(Hin : (φ → ψ0) ∈ Γ')by ms.
  rw Heq 0. destruct HPψ.
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