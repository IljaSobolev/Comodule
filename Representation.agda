open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Category.Instance.Sets using (Sets)

open import Comodule using (IsComodule)
open import Cont

module Representation
  (M : Monad Cont)
  (c : NaturalTransformation ⟪⟫ (⟪⟫ ∘F (Functor.op (Monad.F M))))
  (isComodule : IsComodule M _ ⟪⟫ c)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≗_)
open import Function using (_∘_; id)

open import Categories.Category using (Category)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Category.Construction.Kleisli using (Kleisli)

open Monad M renaming (F to T; η to Tη; μ to Tμ)
open T renaming (F₀ to T₀; F₁ to T₁)

open NaturalTransformation c
open IsComodule isComodule


-- COMODULE REPRESENTATION OF FUNCTIONALS

represents : D ⇒ T₀ C → (⟪ C ⟫₀ → ⟪ D ⟫₀) → Set
represents f F = ⟪ f ⟫₁ ∘ η _ ≗ F


-- IDENTITY FUNCTIONAL IS REPRESENTABLE

id-representable : represents (Tη.η C) id
id-representable x = identity isComodule x


-- COMPOSITION OF REPRESENTABLE FUNCTIONALS IS REPRESENTABLE

comm : (f : D ⇒ T₀ C) (g : E ⇒ T₀ D) → ⟪ Tμ.η C ∘C T₁ f ∘C g ⟫₁ ∘ η _ ≗ ⟪ g ⟫₁ ∘ η _ ∘ ⟪ f ⟫₁ ∘ η _
comm f g =
  begin
    ⟪ g ⟫₁ ∘ ⟪ T₁ f ⟫₁ ∘ ⟪ Tμ.η _ ⟫₁ ∘ η _
  ≈⟨ refl⟩∘⟨_ {f = ⟪ g ⟫₁ ∘ ⟪ T₁ f ⟫₁} (assoc isComodule) ⟩
    ⟪ g ⟫₁ ∘ ⟪ T₁ f ⟫₁ ∘ η _ ∘ η _
  ≈⟨ refl⟩∘⟨_ {f = ⟪ g ⟫₁} (sym-commute f ∘ η _) ⟩
    ⟪ g ⟫₁ ∘ η _ ∘ ⟪ f ⟫₁ ∘ η _
  ∎
  where
  open Category (Sets _) using (module HomReasoning)
  open HomReasoning

∘-representable : (f : D ⇒ T₀ C) (g : E ⇒ T₀ D)
                  (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) (G : ⟪ D ⟫₀ → ⟪ E ⟫₀) →
                  represents f F →
                  represents g G →
                  represents (Tμ.η C ∘C T₁ f ∘C g) (G ∘ F)
∘-representable f g F G rF rG =
  begin
    ⟪ g ⟫₁ ∘ ⟪ T₁ f ⟫₁ ∘ ⟪ Tμ.η _ ⟫₁ ∘ η _
  ≈⟨ comm f g ⟩
    ⟪ g ⟫₁ ∘ η _ ∘ ⟪ f ⟫₁ ∘ η _
  ≈⟨ rG ⟩∘⟨ rF ⟩
    G ∘ F
  ∎
  where
  open Category (Sets _) using (module HomReasoning)
  open HomReasoning


ℱ : Contravariant (Kleisli M) (Sets _)
ℱ = record
  { F₀ = ⟪_⟫₀
  ; F₁ = λ f → ⟪ f ⟫₁ ∘ η _
  ; identity = id-representable
  ; homomorphism = λ {f = f} {g} → comm f g
  ; F-resp-≈ = λ x _ → cong _ x
  }