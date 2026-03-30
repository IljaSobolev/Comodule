open import Categories.Category using (Category)
open import Categories.Monad.Graded using (GradedMonad)
open import Categories.Category.Monoidal using (MonoidalCategory; Monoidal)

module GradedModComodEquivalence {o o' ℓ ℓ' e e'} {𝒞 : Category o ℓ e} {V : MonoidalCategory o' ℓ' e'} (M : GradedMonad V 𝒞) where

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import GradedModule
open import GradedComodule

open Category using (op)

comod→mod : (𝒟 : Category o ℓ e) → GradedComodule M 𝒟 → GradedModule M (op 𝒟)
comod→mod 𝒟 com = record
  { F = Functor.op F
  ; c = λ v → NaturalTransformation.op (c v)
  ; isGradedModule = record { assoc = assoc ; identity = identity ; coerce = coerce }
  }
  where
  open GradedComodule.GradedComodule com using (F; c; isGradedComodule)
  open IsGradedComodule isGradedComodule

mod→comod : (𝒟 : Category o ℓ e) → GradedModule M (op 𝒟) → GradedComodule M 𝒟
mod→comod 𝒟 mod = record
  { F = Functor.op F
  ; c = λ v → NaturalTransformation.op (c v)
  ; isGradedComodule = record { assoc = assoc ; identity = identity ; coerce = coerce }
  }
  where
  open GradedModule.GradedModule mod using (F; c; isGradedModule)
  open IsGradedModule isGradedModule


open import Relation.Binary.Structures using (module IsEquivalence)

CM : (𝒟 : Category o ℓ e) → Functor (GCoMod M 𝒟) (op (GMod M (op 𝒟)))
CM 𝒟 = record
  { F₀ = comod→mod 𝒟
  ; F₁ = λ f → record { θ = NaturalTransformation.op (θ f) ; comm = comm f}
  ; identity = refl equiv
  ; homomorphism = refl equiv
  ; F-resp-≈ = λ x → x
  }
  where
  open GradedComodule._⇒_ using (θ; comm)
  open NaturalTransformation using (η)
  open Category 𝒟 using (_≈_; equiv)
  open IsEquivalence using (refl)

MC : (𝒟 : Category o ℓ e) → Functor (op (GMod M (op 𝒟))) (GCoMod M 𝒟)
MC 𝒟 = record
  { F₀ = mod→comod 𝒟
  ; F₁ = λ f → record { θ = NaturalTransformation.op (θ f) ; comm = comm f}
  ; identity = refl equiv
  ; homomorphism = refl equiv
  ; F-resp-≈ = λ x → x
  }
  where
  open GradedModule._⇒_ using (θ; comm)
  open NaturalTransformation using (η)
  open Category 𝒟 using (_≈_; equiv)
  open IsEquivalence using (refl)

CM∘MC→id : (𝒟 : Category o ℓ e) → NaturalTransformation (CM 𝒟 ∘F MC 𝒟) idF
CM∘MC→id 𝒟 = ntHelper (record
  { η = λ _ → record
    { θ = ntHelper (record { η = λ _ → id; commute = λ _ → identityʳ ○ ⟺ identityˡ })
    ; comm = identityʳ ○ ⟺ identityˡ}
  ; commute = λ _ → identityˡ ○ ⟺ identityʳ
  })
  where
  open Category 𝒟
  open HomReasoning using (⟺; _○_)

id→CM∘MC : (𝒟 : Category o ℓ e) → NaturalTransformation idF (CM 𝒟 ∘F MC 𝒟)
id→CM∘MC 𝒟 = ntHelper (record
  { η = λ _ → record
    { θ = ntHelper (record { η = λ _ → id; commute = λ _ → identityʳ ○ ⟺ identityˡ })
    ; comm = identityʳ ○ ⟺ identityˡ
    }
  ; commute = λ _ → identityˡ ○ ⟺ identityʳ
  })
  where
  open Category 𝒟
  open HomReasoning using (⟺; _○_)

MC∘CM→id : (𝒟 : Category o ℓ e) → NaturalTransformation (MC 𝒟 ∘F CM 𝒟) idF
MC∘CM→id 𝒟 = ntHelper (record
  { η = λ _ → record
    { θ = ntHelper (record { η = λ _ → id; commute = λ _ → identityˡ ○ ⟺ identityʳ })
    ; comm = identityʳ ○ ⟺ identityˡ}
  ; commute = λ _ → identityˡ ○ ⟺ identityʳ
  })
  where
  open Category 𝒟
  open HomReasoning using (⟺; _○_)

id→MC∘CM : (𝒟 : Category o ℓ e) → NaturalTransformation idF (MC 𝒟 ∘F CM 𝒟)
id→MC∘CM 𝒟 = ntHelper (record
  { η = λ _ → record
    { θ = ntHelper (record { η = λ _ → id; commute = λ _ → identityˡ ○ ⟺ identityʳ })
    ; comm = identityʳ ○ ⟺ identityˡ}
  ; commute = λ _ → identityˡ ○ ⟺ identityʳ
  })
  where
  open Category 𝒟
  open HomReasoning using (⟺; _○_)

gmod≅gcomod : (𝒟 : Category o ℓ e) → StrongEquivalence (GCoMod M 𝒟) (op (GMod M (op 𝒟)))
gmod≅gcomod 𝒟 = record
  { F = CM 𝒟
  ; G = MC 𝒟
  ; weak-inverse = record
    { F∘G≈id = record { F⇒G = CM∘MC→id _ ; F⇐G = id→CM∘MC _ ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
    ; G∘F≈id = record { F⇒G = MC∘CM→id _ ; F⇐G = id→MC∘CM _ ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
    }
  }
  where
  open Category 𝒟