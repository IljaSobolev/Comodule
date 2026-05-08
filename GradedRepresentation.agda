open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)

open import Axiom.Extensionality.Propositional using (Extensionality)

open import Cont
open import GradedComodule using (IsGradedComodule)

module GradedRepresentation
  (ext-≡ : ∀ {a b} → Extensionality a b)
  {o ℓ e} {V : MonoidalCategory o ℓ e}
  M c (isGradedComodule : IsGradedComodule {V = V} M _ ⟪⟫ c)
  where

open import ContCocartesian ext-≡ using (_+ᶜ_; !ᶜ; cont-cocartesian;  ⟪⟫-proj₁; ⟪⟫-proj₂; ⟪⟫-pair; ⟪⟫-×)
open import ContCartesian ext-≡ using (⟨_,_⟩ᶜ; 𝟙ᶜ)

open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; _≗_)
open import Function using (_∘_; id)
open import Level using (0ℓ)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor; MonoidalFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Object.Initial using (IsInitial)

open Cocartesian cont-cocartesian using (coproducts)
open BinaryCoproducts coproducts using (coproduct)

open MonoidalFunctor M using (isMonoidal) renaming (F to T)
open Functor T using () renaming (F₀ to T₀; F₁ to T₁)
open Functor using (₀; ₁)
open IsMonoidalFunctor isMonoidal
open MonoidalCategory V using (U; monoidal)
open Monoidal monoidal using (⊗; unit; _⊗₀_)

open IsGradedComodule isGradedComodule
open NaturalTransformation
open Functor
open Coproduct using (i₁; i₂; [_,_])

open Category (Sets 0ℓ) using (module HomReasoning)
open HomReasoning

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

coercion : (f : D ⇒ ₀ (T₀ v) C)
           (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) →
           ∀ m →
           represents v f F →
           represents v' (η (T₁ m) C ∘C f) F
coercion {v = v} {v' = v'} f F m rF =
  begin
    ⟪ f ⟫₁ ∘ ⟪ η (T₁ m) _ ⟫₁ ∘ η (c v') _
  ≈⟨ refl⟩∘⟨_ {f = ⟪ f ⟫₁} (coerce m) ⟩
    ⟪ f ⟫₁ ∘ η (c v) _
  ≈⟨ rF ⟩
    F
  ∎


-- GRADED REPRESENTABLE FUNCTIONALS HAVE FINITE PRODUCTS

proj₁-representable : represents {C = C +ᶜ D} unit (η ε _ ∘C i₁ coproduct) ⟪⟫-proj₁
proj₁-representable = refl⟩∘⟨ identity isGradedComodule

proj₂-representable : represents {C = C +ᶜ D} unit (η ε _ ∘C i₂ coproduct) ⟪⟫-proj₂
proj₂-representable = refl⟩∘⟨ identity isGradedComodule

pair-representable : (f : D ⇒ ₀ (T₀ v) C) (g : E ⇒ ₀ (T₀ v) C)
                     (F : ⟪ C ⟫₀ → ⟪ D ⟫₀) (G : ⟪ C ⟫₀ → ⟪ E ⟫₀) →
                     represents v f F → represents v g G →
                     represents v ([_,_] coproduct f g) (⟪⟫-pair F G)
pair-representable {v = v} f g F G rF rG =
  begin
    ⟪ [_,_] coproduct f g ⟫₁ ∘ η (c v) _
  ≈⟨ (λ _ → ext-≡ (λ {(inj₁ _) → refl; (inj₂ _) → refl})) ⟩
    ⟪⟫-× ∘ (λ u → ⟪ f ⟫₁ u , ⟪ g ⟫₁ u) ∘ η (c v) _
  ≈⟨ refl⟩∘⟨_ {f = ⟪⟫-×} (λ x → cong₂ _,_ (rF x) (rG x)) ⟩
    ⟪⟫-× ∘ (λ u → F u , G u)
  ≈⟨ (λ _ → ext-≡ (λ {(inj₁ _) → refl; (inj₂ _) → refl})) ⟩
    ⟪⟫-pair F G
  ∎

terminal-representable : represents {C = C} unit !ᶜ (λ _ ())
terminal-representable x = ext-≡ (λ ())


-- THE EQUIVALENCE RELATION ON KLEISLI MAPS

_≈_ : ∃ (λ v → C ⇒ ₀ (T₀ v) D) → ∃ (λ v' → C ⇒ ₀ (T₀ v') D) → Set
(v , f) ≈ (v' , g) = ∀ x → ⟪ f ⟫₁ (η (c v) _ x) ≡ ⟪ g ⟫₁ (η (c v') _ x)

≡-to-≈ : {f g : ∃ (λ v → C ⇒ ₀ (T₀ v) D)} → f ≡ g → f ≈ g
≡-to-≈ refl _ = refl


-- CATEGORY OF GRADED REPRESENTABLE FUNCTIONALS

GRFun : Category _ _ _
GRFun = Category.op record
  { Obj = Container
  ; _⇒_ = λ C D → ∃ λ v → C ⇒ ₀ (T₀ v) D
  ; _≈_ = _≈_
  ; id = _ , η ε _
  ; _∘_ = λ {(v , f) (v' , g) → _ , η (⊗-homo.η _) _ ∘C F₁ (T₀ v') f ∘C g}
  ; equiv = record { refl = λ _ → refl ; sym = λ e x → sym (e x) ; trans = λ e e' x → trans (e x) (e' x) }
  ; ∘-resp-≈ = λ { {g = _ , g} {_ , i} e e' x → trans (comm _ g x) (trans (e' _) (trans (cong (⟪ i ⟫₁ ∘ η (c _) _) (e _)) (sym (comm _ i x)))) }
  }


-- CHARACTERISATION OF INITIAL OBJECT IN GRFUN

⇐init : IsInitial GRFun C → ∃ λ v → 𝟙ᶜ ⇒ ₀ (T₀ v) C
⇐init i = IsInitial.! i {𝟙ᶜ}

⇒init : ∃ (λ v → 𝟙ᶜ ⇒ ₀ (T₀ v) C) → IsInitial GRFun C
⇒init (v , f) = record { ! = _ , _ ⊲ λ _ x → ⊥-elim (_⇒_.pf f _ x) ; !-unique = λ _ x → ⊥-elim (_⇒_.pf f _ (η (c _) _ x _)) }