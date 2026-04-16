open import Axiom.Extensionality.Propositional using (Extensionality)

open import Cont

open import Comodule using (IsComodule)
module Representation
  (ext-≡ : ∀ {a b} → Extensionality a b)
  M c (isComodule : IsComodule M _ ⟪⟫ c)
  where

open import ContCocartesian ext-≡ using (_+ᶜ_; !ᶜ; cont-cocartesian; ⟪⟫-proj₁; ⟪⟫-proj₂; ⟪⟫-pair; ⟪⟫-×)
open import ContCartesian ext-≡ using (⟨_,_⟩ᶜ)

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; _≗_; isEquivalence)
open import Function using (_∘_; id)
open import Level using (0ℓ)

open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category using (Category)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Object.Coproduct using (Coproduct)
open Cocartesian cont-cocartesian using (coproducts)
open BinaryCoproducts coproducts using (coproduct)

open Monad M renaming (F to T; η to Tη; μ to Tμ)
open T renaming (F₀ to T₀; F₁ to T₁)

open NaturalTransformation c
open IsComodule isComodule
open Coproduct using (i₁; i₂; [_,_])

open Category (Sets 0ℓ) using (module HomReasoning)
open HomReasoning


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


ℱ₁ : (f : C ⇒ T₀ D) → ⟪ D ⟫₀ → ⟪ C ⟫₀
ℱ₁ f = ⟪ f ⟫₁ ∘ η _

ℱ : Contravariant (Kleisli M) (Sets _)
ℱ = record
  { F₀ = ⟪_⟫₀
  ; F₁ = ℱ₁
  ; identity = id-representable
  ; homomorphism = λ {f = f} {g} → comm f g
  ; F-resp-≈ = λ x _ → cong _ x
  }


-- ℱ PRESERVES FINITE PRODUCTS

proj₁-representable : represents {C = C +ᶜ D} (Tη.η _ ∘C i₁ coproduct) ⟪⟫-proj₁
proj₁-representable = refl⟩∘⟨ identity isComodule

proj₂-representable : represents {C = C +ᶜ D} (Tη.η _ ∘C i₂ coproduct) ⟪⟫-proj₂
proj₂-representable = refl⟩∘⟨ identity isComodule

pair-representable : (f : D ⇒ T₀ C) (g : E ⇒ T₀ C)
                     (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) (G : ⟪ C ⟫₀ → ⟪ E ⟫₀) →
                     represents f F → represents g G →
                     represents ([_,_] coproduct f g) (⟪⟫-pair F G)
pair-representable f g F G rF rG =
  begin
    ⟪ [_,_] coproduct f g ⟫₁ ∘ η _
  ≈⟨ (λ _ → ext-≡ (λ {(inj₁ _) → refl; (inj₂ _) → refl})) ⟩
    ⟪⟫-× ∘ (λ u → ⟪ f ⟫₁ u , ⟪ g ⟫₁ u) ∘ η _
  ≈⟨ refl⟩∘⟨_ {f = ⟪⟫-×} (λ x → cong₂ _,_ (rF x) (rG x)) ⟩
    ⟪⟫-× ∘ (λ u → F u , G u)
  ≈⟨ (λ _ → ext-≡ (λ {(inj₁ _) → refl; (inj₂ _) → refl})) ⟩
    ⟪⟫-pair F G
  ∎

terminal-representable : represents {C = C} !ᶜ (λ _ ())
terminal-representable x = ext-≡ (λ ())