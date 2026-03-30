open import Categories.Category using (Category)
open import Categories.Monad.Graded using (GradedMonad)
open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)

module GradedModule {o o' ℓ ℓ' e e'} {𝒞 : Category o ℓ e} {V : MonoidalCategory o' ℓ' e'} (M : GradedMonad V 𝒞) (𝒟 : Category o ℓ e) where

open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor; MonoidalFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_) renaming (id to ntid)

open MonoidalFunctor M using (isMonoidal) renaming (F to T)
open Functor T using () renaming (F₀ to T₀; F₁ to T₁)
open Functor using (₀)
open Category 𝒟 hiding (_⇒_)
open IsMonoidalFunctor isMonoidal using (ε; ⊗-homo)
open MonoidalCategory V using (U; monoidal)
open Monoidal monoidal using (⊗; unit; _⊗₀_)

record IsGradedModule (F : Functor 𝒞 𝒟) (c : ∀ v → NaturalTransformation (F ∘F T₀ v) F) : Set (o ⊔ o' ⊔ ℓ' ⊔ e) where
  private
    open Functor F using (F₁)
    open NaturalTransformation using (η)
    module U = Category U
  field
    assoc : ∀ {X v v'} → η (c (v ⊗₀ v')) X ∘ F₁ (η (⊗-homo.η (v , v')) X) ≈ η (c v') X ∘ η (c v) (₀ (T₀ v') X)
    identity : ∀ {X} → η (c unit) X ∘ F₁ (η ε X) ≈ id
    coerce : ∀ {X v v'} (m : v U.⇒ v') → η (c v') X ∘ F₁ (η (T₁ m) X) ≈ η (c v) X

record GradedModule : Set (o ⊔ o' ⊔ ℓ ⊔ ℓ' ⊔ e) where
  field
    F              : Functor 𝒞 𝒟
    c              : ∀ v → NaturalTransformation (F ∘F T₀ v) F
    isGradedModule : IsGradedModule F c

record _⇒_ (X Y : GradedModule) : Set (o ⊔ o' ⊔ ℓ ⊔ e) where
  module X = GradedModule X
  module Y = GradedModule Y
  open NaturalTransformation using (η)
  field
    θ    : NaturalTransformation X.F Y.F
    comm : ∀ {X v} → η θ X ∘ η (X.c v) X ≈ η (Y.c v) X ∘ η θ (₀ (T₀ v) X)

GMod : Category _ _ _
GMod = record
  { Obj = GradedModule
  ; _⇒_ = _⇒_
  ; _≈_ = λ x y → ∀ {X} → η (θ x) X ≈ η (θ y) X
  ; id = record { θ = ntid ; comm = identityˡ ○ ⟺ identityʳ }
  ; _∘_ = λ x y → record { θ = θ x ∘ᵥ θ y ; comm = assoc ○ refl⟩∘⟨ comm y ○ sym-assoc ○ comm x ⟩∘⟨refl ○ assoc}
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl; sym = λ z → ⟺ z ; trans = λ x y → x ○ y }
  ; ∘-resp-≈ = λ x y → x ⟩∘⟨ y
  }
  where
  open _⇒_ using (θ; comm)
  open NaturalTransformation using (η)
  open HomReasoning using (refl⟩∘⟨_; _⟩∘⟨refl; _⟩∘⟨_; ⟺; _○_)