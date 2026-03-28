open import Categories.Category using (Category)
open import Categories.Monad using (Monad)

module Equiv {o ℓ e} {𝒞 : Category o ℓ e} (M : Monad 𝒞) where

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Module
open import Comodule

open Category using (op)

comod→mod : (𝒟 : Category o ℓ e) → Comodule M 𝒟 → Module M (op 𝒟)
comod→mod 𝒟 com = record
  { F = Functor.op F
  ; c = NaturalTransformation.op c
  ; isModule = record { assoc = ⟺ assoc; identity = identity }
  }
  where
  open Comodule.Comodule com using (F; c; isComodule)
  open IsComodule isComodule using (assoc; identity)
  open Category 𝒟 using (module HomReasoning)
  open HomReasoning using (⟺)

mod→comod : (𝒟 : Category o ℓ e) → Module M (Category.op 𝒟) → Comodule M 𝒟
mod→comod 𝒟 mod = record
  { F = Functor.op F
  ; c = NaturalTransformation.op c
  ; isComodule = record { assoc = ⟺ assoc; identity = identity }
  }
  where
  open Module.Module mod using (F; c; isModule)
  open IsModule isModule using (assoc; identity)
  open Category 𝒟 using (module HomReasoning)
  open HomReasoning using (⟺)

open import Relation.Binary.Structures using (module IsEquivalence)

CM : (𝒟 : Category o ℓ e) → Functor (CoMod M 𝒟) (op (Mod M (op 𝒟)))
CM 𝒟 = record
  { F₀ = comod→mod 𝒟
  ; F₁ = λ f → record { θ = NaturalTransformation.op (θ f) ; comm = comm f}
  ; identity = refl equiv
  ; homomorphism = refl equiv
  ; F-resp-≈ = λ x → x
  }
  where
  open Comodule._⇒_ using (θ; comm)
  open NaturalTransformation using (η)
  open Category 𝒟 using (_≈_; equiv)
  open IsEquivalence using (refl)

MC : (𝒟 : Category o ℓ e) → Functor (op (Mod M (op 𝒟))) (CoMod M 𝒟)
MC 𝒟 = record
  { F₀ = mod→comod 𝒟
  ; F₁ = λ f → record { θ = NaturalTransformation.op (θ f) ; comm = comm f}
  ; identity = refl equiv
  ; homomorphism = refl equiv
  ; F-resp-≈ = λ x → x
  }
  where
  open Module._⇒_ using (θ; comm)
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

mod≅comod : (𝒟 : Category o ℓ e) → StrongEquivalence (CoMod M 𝒟) (op (Mod M (op 𝒟)))
mod≅comod 𝒟 = record
  { F = CM 𝒟
  ; G = MC 𝒟
  ; weak-inverse = record
    { F∘G≈id = record { F⇒G = CM∘MC→id _ ; F⇐G = id→CM∘MC _ ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
    ; G∘F≈id = record { F⇒G = MC∘CM→id _ ; F⇐G = id→MC∘CM _ ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
    }
  }
  where
  open Category 𝒟