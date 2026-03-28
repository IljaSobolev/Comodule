open import Categories.Monad.Graded using (GradedMonad)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor; MonoidalFunctor)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)

open import GradedComodule using (IsGradedComodule)
open import Cont

module GradedRepresentation
  {o ℓ e}
  {V : MonoidalCategory o ℓ e}
  (M : GradedMonad V Cont)
  (c : ∀ v → NaturalTransformation ⟪⟫ (⟪⟫ ∘F (Functor.op (Functor.₀ (MonoidalFunctor.F M) v))))
  (isGradedComodule : IsGradedComodule M _ ⟪⟫ c)
  where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≗_)
open import Function using (_∘_; id)

open import Categories.Category using (Category)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Category.Construction.Kleisli using (Kleisli)

open MonoidalFunctor M using (isMonoidal) renaming (F to T)
open Functor T using () renaming (F₀ to T₀; F₁ to T₁)
open Functor using (₀; ₁)
open IsMonoidalFunctor isMonoidal
open MonoidalCategory V using (U; monoidal)
open Monoidal monoidal using (⊗; unit; _⊗₀_)

open IsGradedComodule isGradedComodule
open NaturalTransformation
open Functor

variable
  v v' : Category.Obj U


-- GRADED COMODULE REPRESENTATION OF FUNCTIONALS

represents : ∀ v → D ⇒ ₀ (T₀ v) C → (⟪ C ⟫₀ → ⟪ D ⟫₀) → Set
represents v f F = ⟪ f ⟫₁ ∘ η (c v) _ ≗ F


-- IDENTITY FUNCTIONAL IS REPRESENTABLE

id-representable : represents unit (η ε C) id
id-representable x = identity isGradedComodule x


-- COMPOSITION OF REPRESENTABLE FUNCTIONALS IS REPRESENTABLE

comm : (f : D ⇒ ₀ (T₀ v) C) (g : E ⇒ ₀ (T₀ v') D) →
       ⟪ η (⊗-homo.η (v' , v)) _ ∘C F₁ (T₀ v') f ∘C g ⟫₁ ∘ η (c (v' ⊗₀ v)) _
       ≗
       ⟪ g ⟫₁ ∘ η (c v') _ ∘ ⟪ f ⟫₁ ∘ η (c v) _
comm {v = v} {v' = v'} f g =
  begin
    ⟪ g ⟫₁ ∘ ⟪ F₁ (T₀ v') f ⟫₁ ∘ ⟪ η (⊗-homo.η (v' , v)) _ ⟫₁ ∘ η (c (v' ⊗₀ v)) _
  ≈⟨ refl⟩∘⟨_ {f = ⟪ g ⟫₁ ∘ ⟪ F₁ (T₀ v') f ⟫₁} (IsGradedComodule.assoc isGradedComodule) ⟩
    ⟪ g ⟫₁ ∘ ⟪ F₁ (T₀ v') f ⟫₁ ∘ η (c v') _ ∘ η (c v) _
  ≈⟨ refl⟩∘⟨_ {f = ⟪ g ⟫₁} (sym-commute (c v') f ∘ η (c v) _) ⟩
    ⟪ g ⟫₁ ∘ η (c v') _ ∘ ⟪ f ⟫₁ ∘ η (c v) _
  ∎
  where
  open Category (Sets _) using (module HomReasoning)
  open HomReasoning

∘-representable : (f : D ⇒ ₀ (T₀ v) C) (g : E ⇒ ₀ (T₀ v') D)
                  (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) (G : ⟪ D ⟫₀ → ⟪ E ⟫₀) →
                  represents v f F →
                  represents v' g G →
                  represents (v' ⊗₀ v) (η (⊗-homo.η (v' , v)) _ ∘C F₁ (T₀ v') f ∘C g) (G ∘ F)
∘-representable {v = v} {v' = v'} f g F G rF rG =
  begin
    ⟪ g ⟫₁ ∘ ⟪ F₁ (T₀ v') f ⟫₁ ∘ ⟪ η (⊗-homo.η (v' , v)) _ ⟫₁ ∘ η (c (v' ⊗₀ v)) _
  ≈⟨ comm f g ⟩
    ⟪ g ⟫₁ ∘ η (c v') _ ∘ ⟪ f ⟫₁ ∘ η (c v) _
  ≈⟨ rG ⟩∘⟨ rF ⟩
    G ∘ F
  ∎
  where
  open Category (Sets _) using (module HomReasoning)
  open HomReasoning