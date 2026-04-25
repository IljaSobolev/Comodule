open import Cont
open import Categories.Monad using (Monad)

module AlgebraRepresentation (M : Monad Cont) where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≗_)
open import Function using (_∘_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ᵥ_; _∘ʳ_)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Construction.EilenbergMoore M using (Module)

open import ContMonoidal using (Idᶜ)
open import Representation M using (represents)

open import Comodule using (IsComodule)

open NaturalTransformation using (η; commute)
open Monad M using () renaming (F to T; η to Tη; μ to Tμ)
open T using () renaming (F₀ to T₀; F₁ to T₁; homomorphism to Thomo)
open _⇒_


-- CONTRAVARIANT HOM FUNCTOR INTO SETS

Hom[-,_] : Container → Contravariant Cont (Sets _)
Hom[-,_] C = record
  { F₀ = _⇒ C
  ; F₁ = λ z → _∘C z
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ {refl _ → refl}
  }


-- COINTERPRETATION FUNCTOR IS REPRESENTABLE

⟪⟫-to-⇒Idᶜ : ⟪ C ⟫₀ → C ⇒ Idᶜ
⟪⟫-to-⇒Idᶜ p = _ ⊲ λ s _ → p s

⇒Idᶜ-to-⟪⟫ : C ⇒ Idᶜ → ⟪ C ⟫₀
⇒Idᶜ-to-⟪⟫ f = ⟪ f ⟫₁ _

⟪⟫-to-hom : NaturalTransformation ⟪⟫ Hom[-, Idᶜ ]
⟪⟫-to-hom = record { η = λ _ → ⟪⟫-to-⇒Idᶜ ; commute = λ _ _ → refl ; sym-commute = λ _ _ → refl }

hom-to-⟪⟫ : NaturalTransformation Hom[-, Idᶜ ] ⟪⟫
hom-to-⟪⟫ = record { η = λ _ → ⇒Idᶜ-to-⟪⟫ ; commute = λ _ _ → refl ; sym-commute = λ _ _ → refl }


-- MONAD ALGEBRAS (MODULES)

record IsModule C : Set where
  field
    action   : T₀ C ⇒ C
    commute  : action ∘C T₁ action ≡ action ∘C Tμ.η C
    identity : action ∘C Tη.η C ≡ idC


-- MONAD ALGEBRA FROM A COMODULE STRUCTURE MAP

module CA c (com : Comodule.IsComodule M _ ⟪⟫ c) where

  open IsComodule com using (assoc)

  cα : NaturalTransformation Hom[-, Idᶜ ] (Hom[-, Idᶜ ] ∘F T.op)
  cα = (⟪⟫-to-hom ∘ʳ T.op) ∘ᵥ c ∘ᵥ hom-to-⟪⟫

  α : IsModule Idᶜ
  α = record
    { action = η cα _ _
    ; commute = sym (trans (cong ⟪⟫-to-⇒Idᶜ (assoc _)) (commute cα _ _))
    ; identity = refl
    }


-- COMODULE STRUCTURE MAP FROM A MONAD ALGEBRA

module AC (mod : IsModule Idᶜ) where

  open IsModule mod using (action) renaming (commute to mod-commute)

  cα : NaturalTransformation Hom[-, Idᶜ ] (Hom[-, Idᶜ ] ∘F T.op)
  cα = ntHelper record { η = λ _ f → action ∘C T₁ f ; commute = λ f g → cong (action ∘C_) (Thomo {g = g}) }

  c : NaturalTransformation ⟪⟫ (⟪⟫ ∘F T.op)
  c = (hom-to-⟪⟫ ∘ʳ T.op) ∘ᵥ cα ∘ᵥ ⟪⟫-to-hom

  assoc-aux : ∀ f → η cα _ (η cα _ f) ≡ η cα C f ∘C Tμ.η _
  assoc-aux f = trans (commute cα (T₁ f) action) (trans (cong (_∘C T₁ (T₁ f)) mod-commute) (cong (action ∘C_) (Tμ.commute f)))

  identity-aux : ∀ f → f ≡ η cα C f ∘C Tη.η C
  identity-aux f = cong (action ∘C_) (Tη.commute f)

  com : Comodule.IsComodule M _ ⟪⟫ c
  com = record
    { assoc = λ _ → sym (cong ⇒Idᶜ-to-⟪⟫ (assoc-aux _))
    ; identity = λ _ → sym (cong ⇒Idᶜ-to-⟪⟫ (identity-aux _))
    }


-- ALGEBRA REPRESENTABLE FUNCTIONALS

representsᵃ : IsModule Idᶜ → D ⇒ T₀ C → (C ⇒ Idᶜ → D ⇒ Idᶜ) → Set
representsᵃ mod f F = ∀ x → IsModule.action mod ∘C T₁ x ∘C f ≡ F x


-- LOGICAL EQUIVALENCE BETWEEN THE TWO NOTIONS OF REPRESENTABILITY

alg→com : ∀ mod (f : D ⇒ T₀ C) (F : C ⇒ Idᶜ → D ⇒ Idᶜ) →
          representsᵃ mod f F →
          -------------------------------
          represents (AC.c mod) (AC.com mod) f (⇒Idᶜ-to-⟪⟫ ∘ F ∘ ⟪⟫-to-⇒Idᶜ)

alg→com mod f F rF x = cong ⇒Idᶜ-to-⟪⟫ (rF (⟪⟫-to-⇒Idᶜ x))

com→alg : ∀ c com (f : D ⇒ T₀ C) (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) →
          represents c com f F →
          -------------------------------
          representsᵃ (CA.α c com) f (⟪⟫-to-⇒Idᶜ ∘ F ∘ ⇒Idᶜ-to-⟪⟫)

com→alg c com f F rF x = trans (cong (_∘C f) (sym (commute (CA.cα c com) x _))) (cong ⟪⟫-to-⇒Idᶜ (rF (⇒Idᶜ-to-⟪⟫ x)))