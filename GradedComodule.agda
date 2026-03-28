open import Categories.Category using (Category)
open import Categories.Monad.Graded using (GradedMonad)
open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)

module GradedComodule {o o' ℓ ℓ' e e'} {𝒞 : Category o ℓ e} {V : MonoidalCategory o' ℓ' e'} (M : GradedMonad V 𝒞) (𝒟 : Category o ℓ e) where

open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor; MonoidalFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_) renaming (id to ntid)

open MonoidalFunctor M using (isMonoidal) renaming (F to T)
open Functor T using () renaming (F₀ to T₀; F₁ to T₁)
open Functor using (₀)
open Category 𝒟 hiding (_⇒_)
open IsMonoidalFunctor isMonoidal
open MonoidalCategory V using (U; monoidal)
open Monoidal monoidal using (⊗; unit; _⊗₀_)

record IsGradedComodule (F : Contravariant 𝒞 𝒟) (c : ∀ v → NaturalTransformation F (F ∘F Functor.op (T₀ v))) : Set (o ⊔ o' ⊔ e) where
  open Functor F using (F₁)
  open NaturalTransformation
  field
    assoc : ∀ {X v v'} → F₁ (η (⊗-homo.η (v , v')) X) ∘ η (c (v ⊗₀ v')) X ≈ η (c v) (₀ (T₀ v') X) ∘ η (c v') X
    identity : ∀ {X} → F₁ (η ε X) ∘ η (c unit) X ≈ id

record GradedComodule : Set (o ⊔ o' ⊔ ℓ ⊔ e) where
  field
    F                : Contravariant 𝒞 𝒟
    c                : ∀ v → NaturalTransformation F (F ∘F Functor.op (T₀ v))
    isGradedComodule : IsGradedComodule F c