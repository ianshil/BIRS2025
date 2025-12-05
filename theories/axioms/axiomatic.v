From Stdlib Require Import Ensembles. (* To use sets. *)
From Stdlib Require Import List. (* To talk about lists (useful in finiteness). *)
Require Import syntax. (* To import the syntax. *)

(* We define here the intuitionistic axioms. *)

(* We use an inductive type to define the property of 
   being an axiom, while it is not really inductive as
   there are not inductive cases...
   But it is a convenient way to store all the axioms
   in one place. *)
Inductive Axioms (φ : form) : Prop :=
  (* The first constructor is called "A1". We can show
     that "φ" is an axiom, i.e. "Axioms φ", via "A1"
     if we can give two formulas "ψ" and "χ" such that
     "φ = (ψ → (χ → ψ))" holds.
     Therefore, we capture with this constructor all
     instances of the axiom "ψ → (χ → ψ)". *)
 | A1 ψ χ : φ = (ψ → (χ → ψ)) -> Axioms φ
 | A2 ψ χ δ : φ = ((ψ → (χ → δ)) → ((ψ → χ) → (ψ → δ))) -> Axioms φ
 | A3 ψ χ : φ = (ψ → (ψ ∨ χ)) -> Axioms φ
 | A4 ψ χ : φ = (χ → (ψ ∨ χ)) -> Axioms φ
 | A5 ψ χ δ : φ = ((ψ → δ) → ((χ → δ) → ((ψ ∨ χ) → δ))) -> Axioms φ
 | A6 ψ χ : φ = ((ψ ∧ χ) → ψ) -> Axioms φ
 | A7 ψ χ : φ = ((ψ ∧ χ) → χ) -> Axioms φ
 | A8 ψ χ δ : φ = ((ψ → χ) → ((ψ → δ) → (ψ → (χ ∧ δ)))) -> Axioms φ
 | A9 ψ : φ = (⊥ → ψ) -> Axioms φ.

(* We can then define the generalised Hilbert system for IPL. 
   What we more precisely capture is the notion of provability
   of a consecution "Γ ⊢ φ", as "⊢" takes a set "Γ"
   and a formula "φ" and returns into "Prop". *)
Reserved Notation "Γ ⊢ φ" (at level 90).
Inductive IHP_prv : (form -> Prop) -> form -> Prop :=
  (* We first encode the identity rule: if "φ ∈ Γ" then "Γ ⊢ φ" *)
  | Id Γ φ : Γ φ -> Γ ⊢ φ
  (* Second, we have the axiom rule: if "φ" is an "Axioms" then "Γ ⊢ φ" *)
  | Ax Γ φ : Axioms φ -> Γ ⊢ φ
  (* Finally, we have the modus ponens rule: 

    Γ ⊢ φ → ψ       Γ ⊢ φ
    ---------------------
           Γ ⊢ ψ                          *)
  | MP Γ φ ψ : Γ ⊢ (φ → ψ) -> Γ ⊢ φ -> Γ ⊢ ψ
  where "Γ ⊢ φ" := (IHP_prv Γ φ).







Section logic.

(* We can now prove stuff about our calculus. 

   We start by showing that our system captures a logic: 
   it is monotonous (weakening of the context),
   compositional (some sort of generalised cut),
   structural (stable over substitutions).
   It is in fact a finitary logic (compactness). *)

(* Monotonicity *)

Theorem IPH_monot : forall Γ φ, 
          Γ ⊢ φ ->                     
          forall Γ', (Included _ Γ Γ') ->     (* Γ ⊆ Γ' *)
          Γ' ⊢ φ.                      
Proof.
intros Γ φ D0. 
(* As "⊢" is defined inductively, we can
   prove our goal by induction on "D0". 
   In essence, this is an induction on the
   structure of the proof "D0". *)
induction D0 ; intros Γ' incl.
(* We have three cases to deal with, one for each rule. *)
(* Id *)
- apply Id ; apply incl ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with φ ; auto.
(* Note here again that we had to specify which formula we
   wanted to apply MP with: Rocq cannot guess what the antecedent
   of the implication is. We can specify it, as we did, or
   do something else which we will shortly see. *)
Qed.

(* Compositionality *)

Theorem IPH_comp : forall Γ φ,
          Γ ⊢ φ ->                                   
          forall Γ', (forall ψ, Γ ψ -> Γ' ⊢ ψ) ->    
          Γ' ⊢ φ.                                    
Proof.
intros Γ φ D0.
induction D0 ; intros Γ' derall ; auto.
(* Rocq manages to automatically solve the case where the
   rule applied was Id! *)
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with φ ; auto.
Qed.

(* Axioms are stable under substitutions. *)

Lemma subst_Ax : forall φ σ, (Axioms φ) -> (Axioms (subst σ φ)).
Proof.
(* Ugly proof to deal with all cases, i.e. all axioms, at once.

   The only interesting thing to note here is that
   when a tactic tac generates 4 goals, say, we can specify what to
   do for each by doing the following: 
   "tac ; [ tac1 | tac2 | tac3 | tac4]".
   The squared brackets and vertical bars separate each of the
   generated subgoals, to which we apply the appropriate tactic. 
   Leaving such a compartment blank is fine: Rocq just won't apply
   anything (handy if we want to solve some of the subgoals directly
   but leave the complex ones for later). *)
intros φ σ Ax. destruct Ax ; subst ; cbn ; 
   [ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
     eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
     eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity].
Qed.

(* Structurality *)

Theorem IPH_struct : forall Γ φ,
          Γ ⊢ φ ->                                                    
          forall σ,   
          (fun y => exists ψ, Γ ψ /\ y = (subst σ ψ)) ⊢ (subst σ φ).   (* σ(Γ) ⊢ σ(φ) *)
Proof.
intros Γ φ D0. induction D0 ; intros σ.
(* Id *)
- apply Id ; unfold In ; exists φ ; auto.
(* Ax *)
- apply Ax. apply subst_Ax ; auto.
(* MP *)
- cbn in *. apply MP with (subst σ φ) ; auto.
Qed.

(* Finiteness *)

Theorem IPH_finite : forall Γ φ,
          Γ ⊢ φ ->                     
          exists Γ', Included _ Γ' Γ /\     (* Γ' ⊆ Γ *)
                      (Γ' ⊢ φ) /\       
                exists l, forall ψ, (Γ' ψ -> List.In ψ l) /\ (List.In ψ l -> Γ' ψ).
                (* Γ' has the same elements as l, hence is finite. *)
Proof.
intros Γ φ D0. induction D0.
(* Id *)
- (* Our goal is existentially quantified, so we need
     to provide a witness: the finite set we are looking for.
     We do this using "exists". *)
  exists (fun x => x = φ).
  (* Now, our goal is a conjunction of 3 elements.
     To prove it, we show that each of the disjuncts
     holds by breaking down the conjunction using "split".
     We need to "repeat" this operation, as really our goal
     is a conjunction of the form "A /\ (B /\ C)". *)
  repeat split ; auto.
  + intros B HB.
    (* "HB" tells us that "B" is in the set "{x | x = φ}",
       so we can extract the information that "B = φ"
       by using "inversion", a tactic which tries to
       extract as much information from an assumption
       without destructing this assumption. *)
    inversion HB ; auto.
  + apply Id ; auto.
  + (* Now to show that the set we picked is finite, we 
       need to provide a list corresponding to it. *)
    exists [φ].
    intro B. split ; intro HB ; subst.
    * apply in_eq.
    * inversion HB ; [ auto | inversion H0].
(* Ax *)
- exists (Empty_set _). repeat split ; auto.
  + intros B HB ; inversion HB.
  + apply Ax ; auto.
  + exists []. intro B. split ; intro HB ; inversion HB.
(* MP *)
- (* The two induction hypotheses on the premises of MP
     give us the two assumptions "IHD0_1" and "IHD0_2".
     As these are existentials, we can extract their
     witness using "destruct" (note that we used the
     same tactic for disjunctions). 
     We can specify the names of the elements we obtain
     via this destruction by using "as (el1 & el2 & ... & eln)". *)
  destruct IHD0_1 as (Left & HR0 & HR1 & (l0 & Hl0)).
  destruct IHD0_2 as (Right & HL0 & HL1 & (l1 & Hl1)).
  (* Our finite set is just the union of the two finite
     sets "Left" and "Right" obtained via the induction
     hypotheses. *)
  exists (Union _ Left Right). repeat split ; auto.
  + intros C HC ; inversion HC ; subst ; auto.
  + apply MP with φ.
    apply IPH_monot with Left ; auto. intros C HC ; apply Union_introl ; auto.
    apply IPH_monot with Right ; auto. intros C HC ; apply Union_intror ; auto.
  + exists (l0 ++ l1). intro C. split ; intro HC. apply in_or_app ; inversion HC ; subst ; firstorder.
    destruct (in_app_or _ _ _ HC). apply Union_introl ; firstorder. apply Union_intror ; firstorder.
Qed.

(* Nice, now we formally know that intuitionistic logic is
   a finitary logic. Groundbreaking! *)

End logic.







Section properties.

(* Here we prove a bunch of properties (theorems and admissible
   rules) which our calculus ⊢ satisfies. *)

Lemma imp_Id_gen φ Γ : Γ ⊢ (φ → φ).
Proof.
(* To prove this theorem we need to build an axiomatic proof for it.
   As you may guess, we will have to use the rule "MP" quite a few
   times. But as noted before, Rocq cannot infer the antecedent of
   the implication we want to use in "MP". So far, we provided Rocq
   explicitly with the antecedent using "with _ ", but we can avoid
   this. We can add an "e" before "apply" to ask Rocq to apply the 
   tactic even if it cannot infer all the information, and for the
   information it cannot infer create an (implicit) existential
   goal to prove. 
   In a nutshell, we are telling Rocq: I know that you do not know
   what I am doing here, but trust me I will give you the formula later. *)
eapply MP.
(* See how Rocq added a "?φ"? The question mark let us know that
   it is a formula we will have to give later on. *)
- eapply MP.
  + apply Ax. apply A2 with φ (⊤ → ⊥ → ⊤) φ. reflexivity.
    (* By giving the formula above we are providing a bit of
       information to Rocq. Once we applied "reflexivity",
       Rocq can start understanding what "?φ" and "?φ0" are. *)
  + (* In fact from the way we proved the last goal Rocq
       could understand that "?φ0" is "(φ → (⊤ → ⊥ → ⊤) → φ)". *) 
    apply Ax ; eapply A1 ; reflexivity.
- eapply MP.
  + apply Ax. apply A1 with (⊤ → ⊥ → ⊤) φ ; reflexivity.
  + apply Ax ; eapply A1 ; reflexivity.
Qed.

(* The next theorem has a particularly complicated proof...
   A typical example of difficulty of use of axiomatic systems. *)

Lemma Imp_trans : forall φ ψ χ Γ, Γ ⊢ ((φ → ψ) → (ψ → χ) → (φ → χ)).
Proof.
(* If you have some time on your hands, try to extract the pen-and-paper
   proof from the formalised proof below. You can do like Rocq, and have
   question-marked formulas going up the proof and substitute them once
   you gathered enough information when the leaves are proved. *)
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

Lemma Imp_And : forall φ ψ χ Γ, Γ ⊢ ((φ → (ψ → χ)) → ((φ ∧ ψ) → χ)).
Proof.
intros φ ψ χ Γ.
- eapply MP.
  + eapply MP. 
    * (* Now that we have proved lemmas like "Imp_trans", we 
         can reuse them in proofs.*)
       apply Imp_trans.
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

Lemma ND_BotE Γ φ : Γ ⊢ ⊥ -> Γ ⊢ φ.
Proof.
intros Hp.
eapply MP.
- eapply Ax ; eapply A9 ; reflexivity.
- exact Hp.
Qed.

Lemma ND_AndI Γ φ ψ : Γ ⊢ φ -> Γ ⊢ ψ -> Γ ⊢ (φ ∧ ψ).
Proof.
intros Hp1 Hp2.
eapply MP ; [ eapply MP ; [ eapply MP ; [ eapply Ax ; eapply A8 ; reflexivity | apply imp_Id_gen ]| ] | ].
eapply MP ; [ apply Ax ; eapply A1 ; reflexivity | exact Hp2].
exact Hp1.
Qed.

Lemma ND_AndE1 Γ φ ψ : Γ ⊢ (φ ∧ ψ) -> Γ ⊢ φ.
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A6 ; reflexivity | exact Hp ].
Qed.

Lemma ND_AndE2 Γ φ ψ : Γ ⊢ (φ ∧ ψ) -> Γ ⊢ ψ.
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A7 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrI1 Γ φ ψ : Γ ⊢ φ -> Γ ⊢ (φ ∨ ψ).
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A3 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrI2 Γ φ ψ : Γ ⊢ ψ -> Γ ⊢ (φ ∨ ψ).
Proof.
intros Hp.
eapply MP ; [ eapply Ax ; eapply A4 ; reflexivity | exact Hp ].
Qed.

Lemma ND_OrE Γ φ ψ χ : Γ ⊢ (φ ∨ ψ) ->
    Γ ⊢ (φ → χ) -> Γ ⊢ (ψ → χ) -> 
    Γ ⊢ χ.
Proof.
intros Hp1 Hp2 Hp3.
eapply MP ; [ eapply MP ; [ eapply MP ; [ eapply Ax ; eapply A5 ; reflexivity | exact Hp2 ]| exact Hp3 ] | exact Hp1].
Qed.

(* We can finally prove the deduction-detachment theorem, 
   which also mimics the natural deduction rule of implication
   introduction. *)

Theorem Deduction_Detachment_Theorem : forall φ ψ Γ,
                                   (* Γ,φ ⊢ ψ *)
           Γ ⊢ (φ → ψ) <-> (Union _ Γ  (Singleton _ (φ))) ⊢ ψ.
Proof.
intros φ ψ Γ. split.
(* Detachment theorem. The proof is quite easy, and relies
   on "MP". *)
- intro D. eapply MP.
  + apply (IPH_monot Γ (φ → ψ)) ; auto.
    intros C HC. apply Union_introl ; auto.
  + apply Id. right ; split.
(* Deduction theorem. The proof is slightly more
   involved as it goes by induction on the proof
   of Γ,φ ⊢ ψ. *)
- intro D.
  (* When we do an induction on a derivation, Rocq
     may delete information about the context. In this
     case, if we were to do an induction on "D", it would
     erase the information that the context is a union of
     Γ and φ, which is problematic. It does this as the way
     derivations are inductively defined is via a uniform
     context with no specified structure. Induction then
     forces the context to look uniform. To avoid this issue
     we can rename the structured context as a uniform
     one "Γ'". *)
  remember (Union _ Γ (Singleton _ φ)) as Γ'.
  (* Then, we can put back "φ", "Γ" and the equation
     "HeqΓ'" in our goal, so that when we do the induction
     on D our goal has enough information to remember that
     "Γ'" is in fact a union! *)
  revert φ Γ HeqΓ'.
  induction D ; intros χ Γ0 Heq ; subst.
  (* Id *)
  + inversion H ; subst ; cbn.
    * eapply MP.
      -- apply Ax ; eapply A1 ; reflexivity.
      -- apply Id ; auto.
    * inversion H0 ; subst. apply imp_Id_gen.
  (* Ax *)
  + eapply MP.
    * apply Ax ; eapply A1 ; reflexivity.
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

Corollary ND_ImpI : forall φ ψ Γ,
           (Union _ Γ  (Singleton _ (φ))) ⊢ ψ -> Γ ⊢ (φ → ψ).
Proof.
apply Deduction_Detachment_Theorem.
Qed.

(* Now we should have quite enough machinery to smoothly prove
   quite a few theorems. Give the following a try, and / or
   come up with your own lemmas! *)

Lemma And_Imp Γ φ ψ χ : Γ ⊢ (((φ ∧ ψ) → χ) → (φ → ψ → χ)).
Proof.
Admitted.

Lemma unit_or Γ φ ψ : Γ ⊢ (((⊥ ∨ φ) → ψ) → (φ → ψ)).
Proof.
Admitted.

Lemma contraposition Γ φ ψ : Γ ⊢ ((φ → ψ) → (¬ ψ → ¬ φ)).
Proof.
Admitted.

Lemma wLEM Γ φ : Γ ⊢ (¬ ¬ (φ ∨ ¬ φ)).
Proof.
Admitted.

Lemma DisjProp  φ ψ :  (Empty_set _) ⊢ (φ ∨ ψ) ->
      ((Empty_set _) ⊢ φ) \/ ((Empty_set _) ⊢ ψ).
Proof.
(* Good luck. *)
Admitted.

End properties.