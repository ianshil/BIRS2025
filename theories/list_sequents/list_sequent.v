Require Export syntax syntax_facts.

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