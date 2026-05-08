open import Cont
open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)
open import Categories.Monad.Graded using (GradedMonad)
open import Axiom.Extensionality.Propositional using (Extensionality)

module GradedAlgebraRepresentation (ext-≡ : ∀ {a b} → Extensionality a b) {o ℓ e} {V : MonoidalCategory o ℓ e} (M : GradedMonad V Cont) where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≗_)
open import Function using (_∘_)
open import Level using (_⊔_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ᵥ_; _∘ʳ_)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor; MonoidalFunctor)

open import Composition using (Idᶜ)
open import GradedRepresentation ext-≡ M using (represents)
open import GradedComodule using (IsGradedComodule)

open Functor using (₀; ₁; homomorphism)
open NaturalTransformation using (η; commute)
open MonoidalFunctor M using (isMonoidal) renaming (F to T)
open Functor T using () renaming (F₀ to T₀; F₁ to T₁)
open MonoidalCategory V using (U; monoidal)
open Monoidal monoidal
open IsMonoidalFunctor isMonoidal
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


-- GRADED MONAD ALGEBRAS WHOSE UNDERLYING FUNCTOR IS CONSTANT

record IsGradedModule C : Set (o ⊔ ℓ) where
  field
    action   : ∀ m → ₀ (T₀ m) C ⇒ C
    α-nat    : ∀ m n f → action m ∘C η (T₁ f) _ ≡ action n
    commute  : ∀ m n → action m ∘C ₁ (T₀ m) (action n) ≡ action (m ⊗₀ n) ∘C η (⊗-homo.η _) _
    identity : action unit ∘C η ε _ ≡ idC


 -- GRADED MONAD ALGEBRA FROM A GRADED COMODULE STRUCTURE MAP

module CA c (com : GradedComodule.IsGradedComodule M _ ⟪⟫ c) where

  open IsGradedComodule com using (assoc; coerce)

  cα : ∀ v → NaturalTransformation Hom[-, Idᶜ ] (Hom[-, Idᶜ ] ∘F Functor.op (T₀ v))
  cα v = (⟪⟫-to-hom ∘ʳ Functor.op (T₀ v)) ∘ᵥ c v ∘ᵥ hom-to-⟪⟫

  α : IsGradedModule Idᶜ
  α = record
    { action = λ _ → η (cα _) Idᶜ _
    ; α-nat = λ _ _ _ → cong ⟪⟫-to-⇒Idᶜ (coerce _ _)
    ; commute = λ _ _ → sym (trans (cong ⟪⟫-to-⇒Idᶜ (assoc _)) (commute (cα _) _ _))
    ; identity = refl
    }


-- GRADED COMODULE STRUCTURE MAP FROM A GRADED MONAD ALGEBRA

module AC (mod : IsGradedModule Idᶜ) where

  open IsGradedModule mod using (action; α-nat) renaming (commute to mod-commute)

  cα : ∀ v → NaturalTransformation Hom[-, Idᶜ ] (Hom[-, Idᶜ ] ∘F Functor.op (T₀ v))
  cα v = ntHelper record { η = λ _ f → action _ ∘C ₁ (T₀ v) f ; commute = λ f g → cong (action _ ∘C_) (homomorphism (T₀ _) {g = g}) }

  c : ∀ v → NaturalTransformation ⟪⟫ (⟪⟫ ∘F Functor.op (T₀ v))
  c v = (hom-to-⟪⟫ ∘ʳ Functor.op (T₀ v)) ∘ᵥ cα v ∘ᵥ ⟪⟫-to-hom

  assoc-aux : ∀ v w f → action v ∘C ₁ (T₀ v) (action w ∘C ₁ (T₀ w) f) ≡ action (v ⊗₀ w) ∘C ₁ (T₀ (v ⊗₀ w)) f ∘C η (⊗-homo.η _) C
  assoc-aux v w f =
    trans
      (commute (cα _) _ _)
      (trans
        (cong (_∘C ₁ (T₀ v) (₁ (T₀ w) f)) (mod-commute _ _))
        (cong (action _ ∘C_) (commute (⊗-homo.η _) _)))

  identity-aux : ∀ f → f ≡ η (cα _) _ f ∘C η ε C
  identity-aux f = cong (action _ ∘C_) (commute ε f)

  coerce-aux : ∀ v w m (f : C ⇒ Idᶜ) → action v ∘C ₁ (T₀ v) f ≡ action w ∘C ₁ (T₀ w) f ∘C η (T₁ m) _
  coerce-aux v w m f = trans (cong (_∘C ₁ (T₀ v) f) (sym (α-nat _ _ _))) (cong (action _ ∘C_) (commute (T₁ m) f))

  com : GradedComodule.IsGradedComodule M _ ⟪⟫ c
  com = record
    { assoc = λ _ → sym (cong ⇒Idᶜ-to-⟪⟫ (assoc-aux _ _ _))
    ; identity = λ _ → sym (cong ⇒Idᶜ-to-⟪⟫ (identity-aux _))
    ; coerce = λ _ _ → sym (cong ⇒Idᶜ-to-⟪⟫ (coerce-aux _ _ _ _))
    }


-- GRADED ALGEBRA REPRESENTABLE FUNCTIONALS

representsᵃ : IsGradedModule Idᶜ → ∀ v → D ⇒ ₀ (T₀ v) C → (C ⇒ Idᶜ → D ⇒ Idᶜ) → Set
representsᵃ mod v f F = ∀ x → IsGradedModule.action mod v ∘C ₁ (T₀ v) x ∘C f ≡ F x


-- LOGICAL EQUIVALENCE BETWEEN THE TWO NOTIONS OF GRADED REPRESENTABILITY

alg→com : ∀ mod v (f : D ⇒ ₀ (T₀ v) C) (F : C ⇒ Idᶜ → D ⇒ Idᶜ) →
          representsᵃ mod v f F →
          -------------------------------
          represents (AC.c mod) (AC.com mod) v f (⇒Idᶜ-to-⟪⟫ ∘ F ∘ ⟪⟫-to-⇒Idᶜ)

alg→com mod v f F rF x = cong ⇒Idᶜ-to-⟪⟫ (rF (⟪⟫-to-⇒Idᶜ x))

com→alg : ∀ c com v (f : D ⇒ ₀ (T₀ v) C) (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) →
          represents c com v f F →
          -------------------------------
          representsᵃ (CA.α c com) v f (⟪⟫-to-⇒Idᶜ ∘ F ∘ ⇒Idᶜ-to-⟪⟫)

com→alg c com v f F rF x = trans (cong (_∘C f) (sym (commute (CA.cα c com v) x _))) (cong ⟪⟫-to-⇒Idᶜ (rF (⇒Idᶜ-to-⟪⟫ x)))