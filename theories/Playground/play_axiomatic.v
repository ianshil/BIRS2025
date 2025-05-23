Require Import Ensembles.

Require Import syntax.

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