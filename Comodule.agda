open import Categories.Category using (Category)
open import Categories.Monad using (Monad)

module Comodule
  {o ℓ e}
  {𝒞 𝒟 : Category o ℓ e}
  (M : Monad 𝒞)
  where

open Monad M using (μ; η) renaming (F to T)

open import Level using (_⊔_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.NaturalTransformation using (NaturalTransformation)

record IsComodule (F : Contravariant 𝒞 𝒟) (c : NaturalTransformation F (F ∘F T.op)) : Set (o ⊔ e) where

  module c = NaturalTransformation c
  open Category 𝒟

  field
    assoc : ∀ {X} → Functor.₁ F (μ.η X) ∘ c.η X ≈ c.η (Functor.₀ T X) ∘ c.η X
    identity : ∀ {X} → Functor.₁ F (η.η X) ∘ c.η X ≈ id

record Comodule : Set (o ⊔ ℓ ⊔ e) where
  field
    F          : Contravariant 𝒞 𝒟
    c          : NaturalTransformation F (F ∘F T.op)
    isComodule : IsComodule F c