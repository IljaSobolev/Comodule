open import Axiom.Extensionality.Propositional using (Extensionality)

open import Cont

open import Comodule using (IsComodule)
module Representation
  (ext-≡ : ∀ {a b} → Extensionality a b)
  M c (isComodule : IsComodule M _ ⟪⟫ c)
  where

open import ContCocartesian ext-≡ using (_+ᶜ_; !ᶜ; cont-cocartesian; ⟪⟫-proj₁; ⟪⟫-proj₂; ⟪⟫-pair; ⟪⟫-×)
open import ContCartesian ext-≡ using (⟨_,_⟩ᶜ; 𝟙ᶜ; _×ᶜ_)

open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; _≗_; isEquivalence)
open import Function using (_∘_; id)
open import Level using (0ℓ)

open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Object.Initial using (IsInitial)
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


-- THE EQUIVALENCE RELATION ON KLEISLI MAPS

infix 4 _≈_
_≈_ : C ⇒ T₀ D → C ⇒ T₀ D → Set
f ≈ g = ∀ x → ⟪ f ⟫₁ (η _ x) ≡ ⟪ g ⟫₁ (η _ x)

≡-to-≈ : {f g : C ⇒ T₀ D} → f ≡ g → f ≈ g
≡-to-≈ refl _ = refl


-- CATEGORY OF REPRESENTABLE FUNCTIONALS

module KM = Category (Kleisli M)

RFun : Category _ _ _
RFun = Category.op record
  { Obj = Container
  ; _⇒_ = λ C D → C ⇒ T₀ D
  ; _≈_ = _≈_
  ; id = Tη.η _
  ; _∘_ = λ f g → Tμ.η _ ∘C T₁ f ∘C g
  ; assoc = λ {f = f} → ≡-to-≈ (KM.assoc {f = f})
  ; sym-assoc = λ {f = f} → ≡-to-≈ (KM.sym-assoc {f = f})
  ; identityˡ = λ {f = f} → ≡-to-≈ (KM.identityˡ {f = f})
  ; identityʳ = λ {f = f} → ≡-to-≈ (KM.identityʳ {f = f})
  ; identity² = ≡-to-≈ KM.identity²
  ; equiv = record { refl = λ _ → refl ; sym = λ e x → sym (e x) ; trans = λ e e' x → trans (e x) (e' x) }
  ; ∘-resp-≈ = λ {g = g} {i} e e' x → trans (comm _ g x) (trans (e' _) (trans (cong (⟪ i ⟫₁ ∘ η _) (e _)) (sym (comm _ i x))))
  }

RFun→Sets : Functor RFun (Sets _)
RFun→Sets = record
  { F₀ = ⟪_⟫₀
  ; F₁ = λ f → ⟪ f ⟫₁ ∘ η _
  ; identity = id-representable
  ; homomorphism = λ {f = f} {g} → comm f g
  ; F-resp-≈ = id
  }

ℱ : Contravariant (Kleisli M) RFun
ℱ = record
  { F₀ = id
  ; F₁ = id
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ {refl _ → refl}
  }


-- CHARACTERISATION OF INITIAL OBJECT IN RFUN

⇐init : IsInitial RFun C → 𝟙ᶜ ⇒ T₀ C
⇐init i = IsInitial.! i {𝟙ᶜ}

⇒init : 𝟙ᶜ ⇒ T₀ C → IsInitial RFun C
⇒init f = record { ! = _ ⊲ λ _ x → ⊥-elim (_⇒_.pf f _ x) ; !-unique = λ _ x → ⊥-elim (_⇒_.pf f _ (η _ x _)) }