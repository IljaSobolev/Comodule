open import Axiom.Extensionality.Propositional using (Extensionality)

module Representation
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Monad using (Monad)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Cont ext-≡
open import Comodule

-- COINTERPRETATION OF CONTAINERS

⟪_⟫₀ : Container → Set
⟪ S ⊲ P ⟫₀ = ∀ s → P s

⟪_⟫₁ : C ⇒ D → ⟪ D ⟫₀ → ⟪ C ⟫₀
⟪ f ⊲ g ⟫₁ a s = g s (a (f s))

⟪⟫ : Functor (Category.op Cont) (Sets _)
⟪⟫ = record
  { F₀ = ⟪_⟫₀
  ; F₁ = ⟪_⟫₁
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ {refl _ → refl}
  }


-- COMODULE REPRESENTATION OF CONTAINERS

representation : (M : Monad Cont) →
                 (c : NaturalTransformation ⟪⟫ (⟪⟫ ∘F (Functor.op (Monad.F M)))) →
                 IsComodule M ⟪⟫ c →
                 (D ⇒ Functor.₀ (Monad.F M) C) →
                 (⟪ C ⟫₀ → ⟪ D ⟫₀) →
                 Set
representation M c p f F = F ≡ ⟪ f ⟫₁ ∘ NaturalTransformation.η c _