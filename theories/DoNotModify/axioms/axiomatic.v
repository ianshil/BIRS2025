Require Import Ensembles. (* To use sets. *)
Require Import List. (* To talk about lists (useful in finiteness). *)
Export ListNotations.
Require Import syntax. (* To import the syntax. *)

Section axiomatic_calculus.

(* We define here the intuitionistic axioms. *)

Inductive Axioms (φ : form) : Prop :=
 | A1 ψ χ : φ = (ψ → (χ → ψ)) -> Axioms φ
 | A2 ψ χ δ : φ = ((ψ → (χ → δ)) → ((ψ → χ) → (ψ → δ))) -> Axioms φ
 | A3 ψ χ : φ = (ψ → (ψ ∨ χ)) -> Axioms φ
 | A4 ψ χ : φ = (χ → (ψ ∨ χ)) -> Axioms φ
 | A5 ψ χ δ : φ = ((ψ → δ) → ((χ → δ) → ((ψ ∨ χ) → δ))) -> Axioms φ
 | A6 ψ χ : φ = ((ψ ∧ χ) → ψ) -> Axioms φ
 | A7 ψ χ : φ = ((ψ ∧ χ) → χ) -> Axioms φ
 | A8 ψ χ δ : φ = ((ψ → χ) → ((ψ → δ) → (ψ → (χ ∧ δ)))) -> Axioms φ
 | A9 ψ : φ = (⊥ → ψ) -> Axioms φ.

(* We can then define the generalised Hilbert system for IPL. *)

Inductive IPH_prv : (form -> Prop) -> form -> Prop :=
  | Id Γ φ : Γ φ -> IPH_prv Γ φ
  | Ax Γ φ : Axioms φ -> IPH_prv Γ φ
  | MP Γ φ ψ : IPH_prv Γ (φ → ψ) -> IPH_prv Γ φ -> IPH_prv Γ ψ.

End axiomatic_calculus.






Section logic.

(* Here we show that our system captures a logic: 
   it is monotonous (weakening of the context),
   compositional (some sort of generalised cut),
   structural (stable over substitutions).
   It is in fact a finitary logic (compactness). *)

(* Monotonicity *)

Theorem IPH_monot : forall Γ φ,
          IPH_prv Γ φ ->
          forall Γ1, (Included _ Γ Γ1) ->
          IPH_prv Γ1 φ.
Proof.
intros Γ φ D0. induction D0 ; intros Γ1 incl.
(* Id *)
- apply Id ; apply incl ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with φ ; auto.
Qed.

(* Compositionality *)

Theorem IPH_comp : forall Γ φ,
          IPH_prv Γ φ ->
          forall Γ', (forall ψ, Γ ψ -> IPH_prv Γ' ψ) ->
          IPH_prv Γ' φ.
Proof.
intros Γ φ D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with φ ; auto.
Qed.

(* Axioms are stable under substitutions. *)

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms (subst f A)).
Proof.
intros A f Ax. destruct Ax ; subst ; cbn ; 
   [ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
     eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
     eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity].
Qed.

(* Structurality *)

Theorem IPH_struct : forall Γ φ,
          IPH_prv Γ φ ->
          forall (f : nat -> form),
          IPH_prv (fun y => exists ψ, Γ ψ /\ y = (subst f ψ)) (subst f φ).
Proof.
intros Γ φ D0. induction D0 ; intros f.
(* Id *)
- apply Id ; unfold In ; exists φ ; auto.
(* Ax *)
- apply Ax. apply subst_Ax ; auto.
(* MP *)
- cbn in *. apply MP with (subst f φ) ; auto.
Qed.

(* Finiteness *)

Theorem IPH_finite : forall Γ φ,
          IPH_prv Γ φ ->
          exists Fin, Included _ Fin Γ /\
                           IPH_prv Fin φ /\
                           exists l, forall ψ, (Fin ψ -> List.In ψ l) /\ (List.In ψ l -> Fin ψ).
Proof.
intros Γ φ D0. induction D0.
(* Id *)
- exists (fun x => x = φ). repeat split ; auto.
  + intros B HB ; inversion HB ; auto.
  + apply Id ; unfold In ; auto.
  + exists [φ]. intro B. split ; intro HB ; subst. apply in_eq. inversion HB ; auto.
     inversion H0.
(* Ax *)
- exists (Empty_set _). repeat split ; auto.
  + intros B HB ; inversion HB.
  + apply Ax ; auto.
  + exists []. intro B. split ; intro HB ; inversion HB.
(* MP *)
- destruct IHD0_1 as (Left & HR0 & HR1 & (l0 & Hl0)).
  destruct IHD0_2 as (Right & HL0 & HL1 & (l1 & Hl1)).
  exists (Union _ Left Right). repeat split ; auto.
  + intros C HC ; inversion HC ; subst ; auto.
  + apply MP with φ.
     apply IPH_monot with Left ; auto. intros C HC ; apply Union_introl ; auto.
     apply IPH_monot with Right ; auto. intros C HC ; apply Union_intror ; auto.
  + exists (l0 ++ l1). intro C. split ; intro HC. apply in_or_app ; inversion HC ; subst ; firstorder.
     destruct (in_app_or _ _ _ HC). apply Union_introl ; firstorder. apply Union_intror ; firstorder.
Qed.

End logic.







Section properties.

(* Here we prove a bunch of properties (theorems and admissible
   rules) which our calculus IPH_prv satisfies. *)

Lemma Thm_irrel φ ψ Γ : IPH_prv Γ (φ → (ψ → φ)).
Proof.
apply Ax. eapply A1 ; reflexivity.
Qed.

Lemma imp_Id_gen φ Γ : IPH_prv Γ (φ → φ).
Proof.
eapply MP.
- eapply MP.
  + apply Ax. apply A2 with φ (⊤ → ⊥ → ⊤) φ. reflexivity.
  + apply Ax. apply A1 with φ (⊤ → ⊥ → ⊤) ; reflexivity.
- eapply MP.
  + apply Ax. apply A1 with (⊤ → ⊥ → ⊤) φ ; reflexivity.
  + apply Ax. apply A1 with ⊤ ⊥ ; reflexivity.
Qed.

(* The next theorem has a particularly complicated proof...
   A typical example of difficulty of use of axiomatic systems. *)

Lemma Imp_trans : forall φ ψ χ Γ, IPH_prv Γ ((φ → ψ) → (ψ → χ) → (φ → χ)).
Proof.
intros. eapply MP.
- eapply MP.
  + eapply MP.
    * eapply MP ; apply Ax ; eapply A2 ; reflexivity.
    * eapply MP ; apply Ax.
      -- eapply A1 ; reflexivity.
      -- eapply A2 ; reflexivity.
  + eapply MP.
    * apply Ax ; eapply A1 ; reflexivity.
    * eapply MP. 
      -- eapply MP.
        ++ eapply MP ; apply Ax ; eapply A2 ; reflexivity.
        ++ eapply MP.
          ** apply Ax ; eapply A1 ; reflexivity. 
          ** eapply MP ; apply Ax ; eapply A1 ; reflexivity.
      -- eapply MP. 
        ++ eapply MP.
          ** eapply MP ; apply Ax ; eapply A2 ; reflexivity.
          ** eapply MP ; apply Ax ; eapply A1 ; reflexivity.
        ++ eapply MP ; apply Ax.
          ** eapply A1 ; reflexivity.
          ** eapply A2 ; reflexivity.
- eapply MP.
  + eapply MP.
    * eapply MP ; apply Ax ; eapply A2 ; reflexivity.
    * eapply  MP ; apply Ax ; eapply A1 ; reflexivity.
  + eapply MP ; apply Ax.
    * eapply A1 ; reflexivity.
    * eapply A2 ; reflexivity.
Qed.

Lemma Imp_And : forall φ ψ χ Γ, IPH_prv Γ ((φ → (ψ → χ)) → ((φ ∧ ψ) → χ)).
Proof.
intros φ ψ χ Γ.
- eapply MP.
  + eapply MP. 
    * apply Imp_trans.
    * eapply MP.
      -- apply Imp_trans.
      -- apply Ax ; eapply A6 ; reflexivity.
  + eapply MP.
    * eapply MP ; apply Ax ; eapply A2 ; reflexivity.
    * eapply MP.
      -- apply Ax ; eapply A1 ; reflexivity.
      -- apply Ax ; eapply A7 ; reflexivity.
Qed.

(* Because we are not animals, we prove natural deduction rules.
   They are very handy if we want to prove theorems of the logic. 
   Each lemma is named ND for "Natural Deduction", followed by
   the connective it is about (Bot,And,...) and finally by I or E
   for "Introduction" or "Elimination". *)

Lemma ND_BotE Γ φ : IPH_prv Γ ⊥ -> IPH_prv Γ φ.
Proof.
intros Hp.
eapply MP.
- eapply Ax ; eapply A9 ; reflexivity.
- exact Hp.
Qed.

Lemma ND_AndI Γ φ ψ : IPH_prv Γ φ -> IPH_prv Γ ψ -> IPH_prv Γ (φ ∧ ψ).
Proof.
intros Hp1 Hp2.
eapply MP ; [ eapply MP ; [ eapply MP ; [ eapply Ax ; eapply A8 ; reflexivity | apply imp_Id_gen ]| ] | ].
eapply MP ; [ apply Thm_irrel | exact Hp2].
exact Hp1.
Qed.

Lemma ND_AndE1 Γ φ ψ : IPH_prv Γ (φ ∧ ψ) -> IPH_prv Γ φ.
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A6 ; reflexivity | exact Hp ].
Qed.

Lemma ND_AndE2 Γ φ ψ : IPH_prv Γ (φ ∧ ψ) -> IPH_prv Γ ψ.
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A7 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrI1 Γ φ ψ : IPH_prv Γ φ -> IPH_prv Γ (φ ∨ ψ).
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A3 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrI2 Γ φ ψ : IPH_prv Γ ψ -> IPH_prv Γ (φ ∨ ψ).
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A4 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrE Γ φ ψ χ : IPH_prv Γ (φ ∨ ψ) ->
    IPH_prv Γ (φ → χ) -> IPH_prv Γ (ψ → χ) -> 
    IPH_prv Γ χ.
Proof.
intros Hp1 Hp2 Hp3.
eapply MP ; [ eapply MP ; [ eapply MP ; [ eapply Ax ; eapply A5 ; reflexivity | exact Hp2 ]| exact Hp3 ] | exact Hp1].
Qed.

Theorem Deduction_Detachment_Theorem : forall φ ψ Γ,
           IPH_prv Γ (φ → ψ) <-> IPH_prv  (Union _ Γ  (Singleton _ (φ))) ψ.
Proof.
intros φ ψ Γ. split.
(* Detachment theorem. *)
- intro D. eapply MP.
  + apply (IPH_monot Γ (φ → ψ)) ; auto.
    intros C HC. apply Union_introl ; auto.
  + apply Id. right ; split.
- intro D. remember (Union _ Γ (Singleton _ φ)) as Γ'.
  revert φ Γ HeqΓ'.
  induction D ; intros χ Γ0 id ; subst.
  (* Id *)
  + inversion H ; subst ; cbn.
    * eapply MP.
      -- apply Thm_irrel.
      -- apply Id ; auto.
    * inversion H0 ; subst. apply imp_Id_gen.
  (* Ax *)
  + eapply MP.
    * apply Thm_irrel.
    * apply Ax ; assumption.
  (* MP *)
  + eapply MP.
    * eapply MP.
      -- apply Imp_trans.
      -- eapply MP.
        ++ eapply MP.
          ** apply Ax ; eapply A8 ; reflexivity.
          ** apply imp_Id_gen.
        ++ apply IHD2 ; auto.
    * eapply MP.
      -- apply Imp_And.
      -- apply IHD1 ; auto.
Qed.

(* Add more results to formalise. *)

End properties.