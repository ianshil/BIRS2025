
(* PART 1 : SYNTAX *)



(* We can import a library about sets ("ensembles" in French). *)
Require Import Ensembles.
Require Import stdpp.list. (* To deal with lists. *)
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
Require Import Coq.Program.Equality.


Global Instance fomula_bottom : base.Bottom form := Bot.
Global Instance fomula_top : base.Top form := fTop.

Section decidable.

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

End decidable.





























(* PART 3 : LIST-SEQUENT CALCULUS *)

(** ** Definition of provability in G4ip *)
Reserved Notation "Γ ⊢ φ" (at level 90).
Inductive Provable : list form -> form -> Type :=
| PId Γ0 Γ1 p : Γ0 ++ # p :: Γ1 ⊢ (#p)
| BotL Γ0 Γ1 φ : Γ0 ++ ⊥ :: Γ1 ⊢ φ
| AndR Γ φ ψ :
    Γ ⊢ φ -> 
    Γ ⊢ ψ ->
      Γ ⊢ (φ ∧ ψ)
| AndL Γ0 Γ1 φ ψ θ :
    Γ0 ++ φ :: ψ :: Γ1 ⊢ θ ->
      Γ0 ++ (φ ∧ ψ) :: Γ1 ⊢ θ
| OrR1 Γ φ ψ :
    Γ ⊢ φ ->
      Γ ⊢ (φ ∨ ψ)
| OrR2 Γ φ ψ :
    Γ ⊢ ψ ->
      Γ ⊢ (φ ∨ ψ)
| OrL Γ0 Γ1 φ ψ θ :
    Γ0 ++ φ :: Γ1  ⊢ θ ->
    Γ0 ++ ψ :: Γ1 ⊢ θ ->
      Γ0 ++ (φ ∨ ψ) :: Γ1 ⊢ θ
| ImpR Γ φ ψ :
    φ :: Γ ⊢ ψ ->
      Γ ⊢ (φ → ψ)
(* We need to duplicate the rule ImpVar as the order matters. *)
| ImpLVar1 Γ0 Γ1 Γ2 p φ ψ :
    Γ0 ++ # p :: Γ1 ++ φ :: Γ2 ⊢ ψ ->
      Γ0 ++ # p :: Γ1 ++ (# p → φ) :: Γ2 ⊢ ψ
| ImpLVar2 Γ0 Γ1 Γ2 p φ ψ :
    Γ0 ++ φ :: Γ1 ++ # p :: Γ2 ⊢ ψ ->
      Γ0 ++ (# p → φ) :: Γ1 ++ # p :: Γ2 ⊢ ψ
| ImpLAnd Γ0 Γ1 φ1 φ2 φ3 ψ :
    Γ0 ++ (φ1 → (φ2 → φ3)) :: Γ1 ⊢ ψ ->
      Γ0 ++ ((φ1 ∧ φ2) → φ3) :: Γ1 ⊢ ψ
| ImpLOr Γ0 Γ1 φ1 φ2 φ3 ψ :
    Γ0 ++ (φ1 → φ3) :: (φ2 → φ3) :: Γ1 ⊢ ψ ->
      Γ0 ++ ((φ1 ∨ φ2) → φ3) :: Γ1 ⊢ ψ
| ImpLImp Γ0 Γ1 φ1 φ2 φ3 ψ :
    Γ0 ++ (φ2 → φ3) :: Γ1 ⊢ (φ1 → φ2) ->
    Γ0 ++ φ3 :: Γ1 ⊢ ψ ->
      Γ0 ++ ((φ1 → φ2) → φ3) :: Γ1 ⊢ ψ
where "Γ ⊢ φ" := (Provable Γ φ).

Notation "Γ ⊢G4ip φ" := (Provable Γ φ) (at level 90).

Global Hint Constructors Provable : proof.





















(* PART 4 : A PATH TO CONTRACTION *)

(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/SequentProps.v *)

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
Admitted.

Lemma AndL_rev  Γ φ ψ θ: (φ ∧ ψ) :: Γ ⊢ θ -> φ :: ψ :: Γ ⊢ θ.
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
  case (decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0. 
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

Lemma ImpLVar_rev  Γ p φ ψ: (# p) :: (# p → φ) :: Γ ⊢ ψ  → (# p) :: φ :: Γ ⊢ ψ.
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

Lemma ImpL_rev_hp : forall φ Γ ψ θ (Hp : (φ → ψ) :: Γ ⊢ θ),
    { Hp' : ψ :: Γ ⊢ θ | height Hp' <= height Hp}.
Proof.
(* We need to manage a bit our goal so that we can
   more freely use permutations / exchange. *)
enough (forall Γ' θ (Hp : Γ' ⊢G4ip θ), forall φ Γ ψ, Γ' ≡ₚ (φ → ψ) :: Γ -> { Hp' : ψ :: Γ ⊢ θ | height Hp' <= height Hp}).
- intros. destruct (H _ _ Hp φ Γ ψ) ; auto.
  exists x ; auto. 
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
    * pose (PId [ψ] x p).
      destruct (exchange_hp _ (ψ :: Γ') _ p1).
      -- cbn ; apply Permutation_cons ; auto.
      -- exists x0 ; cbn in * ; lia.
  + destruct (in_Permutation Γ' ⊥).
    * assert (In ⊥ ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * pose (BotL [ψ] x φ0).
      destruct (exchange_hp _ (ψ :: Γ') _ p0).
      -- cbn ; apply Permutation_cons ; auto.
      -- exists x0 ; cbn in * ; lia.
  + destruct (IHHp1 _ HH) as [Hp1' Hh1'] ; destruct (IHHp2 _ HH) as [Hp2' Hh2'].
    pose (AndR _ _ _ Hp1' Hp2'). exists p ; cbn ; lia.
  + destruct (in_Permutation Γ' (φ0 ∧ ψ0)).
    * assert (In (φ0 ∧ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * destruct (IHHp (φ0 :: ψ0 :: x)) as [Hp' Hh'].
      -- repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ → ψ)).
         do 2 (apply Permutation_cons ; auto). rewrite <- p in HH.
         repeat rewrite <- Permutation_middle in HH.
         apply (@Permutation_cons_app_inv _ _ [(φ → ψ)]) in HH ; auto.
      -- pose (AndL [ψ] _ _ _ _ Hp').
         destruct (exchange_hp _ (ψ :: Γ') _ p0) ; [ rewrite <- p ; auto |].
         exists x0 ; cbn in * ; lia.
  + destruct (IHHp _ HH) as [Hp' Hh'].
    pose (OrR1 _ _ ψ0 Hp'). exists p ; cbn ; lia.
  + destruct (IHHp _ HH) as [Hp' Hh'].
    pose (OrR2 _ φ0 _ Hp'). exists p ; cbn ; lia.
  + destruct (in_Permutation Γ' (φ0 ∨ ψ0)).
    * assert (In (φ0 ∨ ψ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
      inversion H ; try discriminate ; auto.
    * destruct (IHHp1 (φ0 :: x)) as [Hp1' Hh1'].
      -- repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ → ψ)).
         apply Permutation_cons ; auto. rewrite <- p in HH.
         repeat rewrite <- Permutation_middle in HH.
         apply (@Permutation_cons_app_inv _ _ [(φ → ψ)]) in HH ; auto.
      -- destruct (IHHp2 (ψ0 :: x)) as [Hp2' Hh2'].
        ++ repeat rewrite <- Permutation_middle. repeat rewrite <- (perm_swap (φ → ψ)).
            apply Permutation_cons ; auto. rewrite <- p in HH.
            repeat rewrite <- Permutation_middle in HH.
            apply (@Permutation_cons_app_inv _ _ [(φ → ψ)]) in HH ; auto.
        ++ pose (OrL [ψ] _ _ _ _ Hp1' Hp2').
           destruct (exchange_hp _ (ψ :: Γ') _ p0) ; [ rewrite <- p ; auto |].
           exists x0 ; cbn in * ; lia.
  + destruct (IHHp (φ0 :: Γ')) as [Hp' Hh'].
    * rewrite HH. apply perm_swap.
    * destruct (exchange_hp _ (φ0 :: ψ :: Γ') _ Hp') ; [apply perm_swap | ].
      pose (ImpR _ _ _ x). exists p ; cbn in * ; lia.
  + case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      destruct (exchange_hp _ (ψ :: Γ') _ Hp).
      -- repeat rewrite <- Permutation_middle ; rewrite perm_swap ; apply Permutation_cons ; auto.
         repeat rewrite <- Permutation_middle in HH ; rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
      -- exists x ; cbn in * ; lia.
    * destruct (in_Permutation Γ' (# p → φ0)).
      -- assert (In (# p → φ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; auto).
         inversion H ; [ exfalso ; auto | auto].
      -- rewrite <- p0 in HH. destruct (in_Permutation x (# p)).
        ++ assert (In (# p) ((φ → ψ) :: (# p → φ0) :: x)) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
           inversion H ; [ discriminate | ]. inversion H0 ; [ discriminate | auto].
        ++ rewrite <- p1 in HH.
           destruct (IHHp (φ0 :: # p :: x0)) as [Hp' Hh'].
           ** repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap (#p)) ; apply Permutation_cons ; auto.
              rewrite perm_swap ; apply Permutation_cons ; auto.
              repeat rewrite <- Permutation_middle in HH. repeat rewrite (perm_swap (#p)) in HH ; apply Permutation_cons_inv in HH ; auto.
              rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
           ** pose (ImpLVar2 [ψ] [] _ _ _ _ Hp') ; cbn in p2.
              destruct (exchange_hp _ (ψ :: Γ') _ p2) ; [rewrite p1 ; rewrite p0 ; auto| ].
              exists x1 ; cbn in * ; lia.
  + case (decide ((# p → φ0) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      destruct (exchange_hp _ (ψ :: Γ') _ Hp).
      -- repeat rewrite <- Permutation_middle. apply Permutation_cons ; auto.
         repeat rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
      -- exists x ; cbn in * ; lia.
    * destruct (in_Permutation Γ' (# p → φ0)).
      -- assert (In (# p → φ0) ((φ → ψ) :: Γ')) by (rewrite <- HH ; apply in_or_app ; right ; left ; auto).
         inversion H ; [ exfalso ; auto | auto].
      -- rewrite <- p0 in HH. destruct (in_Permutation x (# p)).
        ++ assert (In (# p) ((φ → ψ) :: (# p → φ0) :: x)) by (rewrite <- HH ; apply in_or_app ; right ; right ; apply in_or_app ; right ; left ; auto).
           inversion H ; [ discriminate | ]. inversion H0 ; [ discriminate | auto].
        ++ rewrite <- p1 in HH.
           destruct (IHHp (φ0 :: # p :: x0)) as [Hp' Hh'].
           ** repeat rewrite <- Permutation_middle. repeat rewrite (perm_swap (#p)) ; apply Permutation_cons ; auto.
              rewrite perm_swap ; apply Permutation_cons ; auto.
              repeat rewrite <- Permutation_middle in HH. repeat rewrite (perm_swap (#p)) in HH ; apply Permutation_cons_inv in HH ; auto.
              rewrite perm_swap in HH ; apply Permutation_cons_inv in HH ; auto.
           ** pose (ImpLVar2 [ψ] [] _ _ _ _ Hp') ; cbn in p2.
              destruct (exchange_hp _ (ψ :: Γ') _ p2) ; [rewrite p1 ; rewrite p0 ; auto| ].
              exists x1 ; cbn in * ; lia.
  + case (decide ((φ1 ∧ φ2 → φ3) = (φ → ψ))); intro Heq0.
    * inversion Heq0 ; subst.
      destruct (exchange_hp _ ((φ1 → φ2 → ψ) :: Γ') _ Hp).
      -- rewrite <- Permutation_middle ; apply Permutation_cons ; auto.
         rewrite <- Permutation_middle in HH ; apply Permutation_cons_inv in HH ; auto.
      -- assert (weight φ1 ≤ w) by (cbn in * ; lia).
         destruct (IHw Γ' _ φ1 (φ2 → ψ) ψ0 H (Permutation_refl _) x) ; auto.
         assert (weight φ2 ≤ w) by (cbn in * ; lia).
         destruct (IHw Γ' _ φ2 ψ ψ0 H0 (Permutation_refl _) x0) ; auto.
         exists x1 ; cbn in * ; lia.
    * (* Need to exhibit "(φ1 ∧ φ2 → φ3)" in "Γ'" and
         apply ImpLAnd, and then apply "IHHp". *) admit.
(* We proceed as in the previous cases for the remaining ones. *)
  + admit.
  + admit.
Admitted.

Lemma ImpL_rev : forall φ Γ ψ θ, (φ → ψ) :: Γ ⊢ θ -> ψ :: Γ ⊢ θ.
Proof.
intros φ Γ ψ θ Hp. destruct (ImpL_rev_hp φ Γ ψ θ Hp) ; auto.
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


































(* PART 5 : CUT ADMISSIBILITY *)

(* This file is a modification of a file by Hugo Férée:
   https://github.com/hferee/UIML/blob/main/theories/iSL/Cut.v *)


Require Arith.

(** * Cut Admissibility *)

Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> φ :: Γ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
(* Primary induction on the weight of the cut formula. *)
induction w; intros φ Hw ; [destruct φ ; cbn in Hw ; lia|].
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
      * intro Hneq.
        (* Need to make "# p" and "# p → φ0" appear in "Γ" (holds because of HeqΓ'),
           and then apply ImpLVar1/2 and then IHh on the resulting proof with Hp2. *) admit.
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
      * intro Hneq. (* Same as above. *) admit.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * intro Heq' ; inversion Heq' ; subst.
        apply (IHw (φ1 → φ2 → ψ0)) ; auto.
        -- cbn in * ; lia.
        -- repeat apply ImpR.
           apply exchange with (φ1 :: φ2 :: Γ) ; [ apply perm_swap | ].
           apply AndL_rev ; auto.
        -- apply exchange with (Γ0 ++ (φ1 → φ2 → ψ0) :: Γ1) ; [ | auto].
           rewrite <- Permutation_middle. apply Permutation_cons ; auto.
           symmetry. apply Permutation_cons_app_inv with (φ1 ∧ φ2 → ψ0) ; rewrite HeqΓ' ; auto.
      * intro Hneq.
        assert (In (φ1 ∧ φ2 → φ3) Γ).
        { assert (In (φ1 ∧ φ2 → φ3) ((φ → ψ0) :: Γ)) by (rewrite <- HeqΓ' ; apply in_or_app ; right ; left ; split).
          inversion H ; [ exfalso ; auto | auto]. }
        apply in_splitT in H as [Γ' [Γ'' Heq]] ; subst.
        apply ImpLAnd. pose (ImpR _ _ _ Hp1).
        destruct (exchange_hp _ ((φ1 ∧ φ2 → φ3) :: Γ' ++ Γ'') _ p) as [Hp2' Hh2'].
        -- rewrite <- Permutation_middle ; auto.
        -- destruct (ImpLAnd_rev_hp _ _ _ _ _ Hp2') as [Hp3 Hh3].
           destruct (exchange_hp _ (Γ' ++ (φ1 → φ2 → φ3) :: Γ'') _ Hp3) as [Hp3' Hh3'].
           ++ rewrite <- Permutation_middle ; auto.
           ++ destruct (exchange_hp _ ((φ → ψ0) :: Γ' ++ (φ1 → φ2 → φ3) :: Γ'') _ Hp2) as [Hp4 Hh4].
              ** repeat rewrite <- Permutation_middle. rewrite perm_swap. apply Permutation_cons ; auto.
                 symmetry. apply Permutation_cons_app_inv with (φ1 ∧ φ2 → φ3). rewrite HeqΓ'.
                 repeat rewrite <- Permutation_middle. apply perm_swap.
              ** apply IHh with (Hp1 :=Hp3') (Hp2 := Hp4) (y:= height Hp3' + height Hp4) ; [ cbn in * ; lia | auto ].
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
  + destruct (ImpL_rev_hp _ _ _ _ Hp2') as [Hp3 Hh3].
    destruct (exchange_hp _ (ψ0 :: Γ0 ++ # p :: Γ1 ++ φ :: Γ2) _ Hp3) as [Hp3' Hh3'].
    * repeat rewrite <- Permutation_middle.
      do 2 (rewrite <- (perm_swap (φ)) ; apply Permutation_cons ; auto).
    * apply IHh with (Hp1 :=Hp1) (Hp2 := Hp3') (y:= height Hp1 + height Hp3') ; [ cbn in * ; lia | auto ].
- apply ImpLVar2. 
  destruct (exchange_hp _ ((# p → φ) :: ψ0 :: Γ0 ++ Γ1 ++ # p :: Γ2) _ Hp2) as [Hp2' Hh2'].
  + repeat rewrite <- Permutation_middle.
    rewrite <- (perm_swap (# p → φ) ψ0) ; apply Permutation_cons ; auto.
  + destruct (ImpL_rev_hp _ _ _ _ Hp2') as [Hp3 Hh3].
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