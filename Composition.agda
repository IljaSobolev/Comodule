module Composition where

open import Cont

open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism Cont using (_≅_)

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂; assocˡ; assocʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (id; _∘_)


-- COMPOSITION AND UNIT

infix 8 _∘ᶜ_
_∘ᶜ_ : Container → Container → Container
(S ⊲ P) ∘ᶜ (S' ⊲ P') = (Σ[ s ∈ S ] (P s → S')) ⊲ λ (s , i) → Σ[ p ∈ P s ] P' (i p)

Idᶜ : Container
Idᶜ = ⊤ ⊲ λ _ → ⊤


-- COMPOSITION IS FUNCTORIAL

∘ᶜ-bifunctor : Bifunctor Cont Cont Cont
∘ᶜ-bifunctor = record
  { F₀ = λ (C , D) → C ∘ᶜ D
  ; F₁ = λ (_ ⊲ g , _ ⊲ g') → _ ⊲ λ _ p → g _ (proj₁ p) , g' _ (proj₂ p)
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ {(refl , refl) → refl}
  }


-- MONOIDAL STRUCTURE BASED ON COMPOSITION AND UNIT

unitorˡ : Idᶜ ∘ᶜ C ≅ C
unitorˡ = record
  { from = _ ⊲ λ _ → tt ,_
  ; to = _ ⊲ λ _ → proj₂
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

unitorʳ : C ∘ᶜ Idᶜ ≅ C
unitorʳ = record
  { from = _ ⊲ λ _ → _, tt
  ; to = _ ⊲ λ _ → proj₁
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

associator : (C ∘ᶜ D) ∘ᶜ E ≅ C ∘ᶜ (D ∘ᶜ E)
associator = record
  { from = _ ⊲ λ _ → assocˡ
  ; to = _ ⊲ λ _ → assocʳ
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

cont-monoidal : Monoidal Cont
cont-monoidal = monoidalHelper Cont (record
   { ⊗ = ∘ᶜ-bifunctor
   ; unit = Idᶜ
   ; unitorˡ = unitorˡ
   ; unitorʳ = unitorʳ
   ; associator = λ {C} {D} {E} → associator {C} {D} {E}
   ; unitorˡ-commute = refl
   ; unitorʳ-commute = refl
   ; assoc-commute = refl
   ; triangle = refl
   ; pentagon = refl
   })