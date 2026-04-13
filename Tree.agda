open import Axiom.Extensionality.Propositional using (Extensionality)

module Tree (ext-≡ : ∀ {a b} → Extensionality a b) where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; cong; cong₂; sym; trans)
open import Function using (_∘_)

open import Cont
open import ContainerMorphismEquality ext-≡
open import Categories.Monad using (Monad)

open Container
open _⇒_

variable
  S S' : Set
  P P' : S → Set
  s p : S


-- TREES AND PATHS

data Tree (S : Set) (P : S → Set) : Set where
  leaf : Tree S P
  node : ∀ s → (P s → Tree S P) → Tree S P

data Path {S} {P} : Tree S P → Set where
  stop : Path leaf
  step : ∀ t → Path (t p) → Path (node s t)

variable
  t : Tree S P


-- TREE MONAD

𝒯 : Container → Container
𝒯 (S ⊲ P) = Tree S P ⊲ Path


-- UNIT OF TREE MONAD

η : ∀ C → C ⇒ 𝒯 C
η _ = (λ s → node s (λ _ → leaf)) ⊲ λ { _ (step {p = p} _ _) → p }


-- GRAFTING

graft : ∀ t → (Path t → Tree S P) → Tree S P
graft leaf f = f stop
graft (node s t) f = node s (λ p → graft (t p) (f ∘ step _))


-- PATH PROJECTIONS, PAIRING AND ITS PROPERTIES

pfst : {f : Path t → Tree S P} → Path (graft t f) → Path t
pfst {t = leaf} _ = stop
pfst {t = node _ _} (step _ q) = step _ (pfst q)

psnd : {f : Path t → Tree S P} (p : Path (graft t f)) → Path (f (pfst p))
psnd {t = leaf} q = q
psnd {t = node _ t} (step {p = p} _ q) = psnd {t = t p} q

ppair : {f : Path t → Tree S P} (p : Path t) → Path (f p) → Path (graft t f)
ppair stop q = q
ppair (step t p) q = step _ (ppair p q)

pfst-ppair : {f : Path t → Tree S P} (p : Path t) (q : Path (f p)) → pfst {t = t} (ppair {f = f} p q) ≅ p
pfst-ppair stop _ = refl
pfst-ppair (step t p) q = cong (step t) (pfst-ppair p q)

psnd-ppair : {f : Path t → Tree S P} (p : Path t) (q : Path (f p)) → psnd {t = t} (ppair {f = f} p q) ≅ q
psnd-ppair stop _ = refl
psnd-ppair (step t p) q = psnd-ppair p q

pair-ppair : {f : Path t → Tree S P} (p : Path (graft t f)) → ppair {f = f} (pfst p) (psnd {t = t} p) ≅ p
pair-ppair {t = leaf} p = refl
pair-ppair {t = node _ t} (step _ p) = cong (step _) (pair-ppair {t = t _} p)

graft-eq : {f f' : Path t → Tree S P} (p : Path (graft t f)) (q : Path (graft t f')) → f ≅ f' →
           pfst {t = t} p ≅ pfst {t = t} q → psnd {t = t} p ≅ psnd {t = t} q → p ≅ q
graft-eq {t = t} p q refl eq eq' = trans (sym (pair-ppair {t = t} p)) (trans (cong₂ (ppair {t = t}) eq eq') (pair-ppair {t = t} q))


-- MULTIPLICATION OF TREE MONAD

μs : Tree (Tree S P) Path → Tree S P
μs leaf = leaf
μs (node s t) = graft s (μs ∘ t)

μp : (t : Tree (Tree S P) Path) → Path (μs t) → Path t
μp leaf _ = stop
μp (node s t) q = step t (μp _ (psnd {t = s} q))

μ : 𝒯 (𝒯 C) ⇒ 𝒯 C
μ = μs ⊲ μp


-- FUNCTORIALITY

𝒯₁s : C ⇒ D → Tree (Shp C) (Pos C) → Tree (Shp D) (Pos D)
𝒯₁s f leaf = leaf
𝒯₁s f (node s t) = node (sf f s) (𝒯₁s f ∘ t ∘ pf f _)

𝒯₁p : (f : C ⇒ D) → ∀ t → Path (𝒯₁s f t) → Path t
𝒯₁p f leaf p = stop
𝒯₁p f (node s t) (step _ p) = step _ (𝒯₁p f _ p)

𝒯₁ : C ⇒ D → 𝒯 C ⇒ 𝒯 D
𝒯₁ f = 𝒯₁s f ⊲ 𝒯₁p f

𝒯₁s-id : ∀ t → 𝒯₁s (idC {C}) t ≅ t
𝒯₁s-id leaf = refl
𝒯₁s-id (node _ _) = cong (node _) (ext-≅ λ _ → 𝒯₁s-id _)

𝒯₁p-id : ∀ t (p : Path (𝒯₁s (idC {C}) t)) → 𝒯₁p (idC {C}) _ p ≅ p
𝒯₁p-id leaf stop = refl
𝒯₁p-id (node _ _) (step _ p) = cong₂ step (ext-≅ (λ _ → sym (𝒯₁s-id _))) (𝒯₁p-id _ p)

𝒯₁-id : 𝒯₁ (idC {C}) ≡ idC
𝒯₁-id = 𝒯₁s-id ⊲-≡' λ _ → trans (𝒯₁p-id _ _)

module _ (f : C ⇒ D) (g : D ⇒ E) where

  𝒯₁s-comp : ∀ t → 𝒯₁s (g ∘C f) t ≅ 𝒯₁s g (𝒯₁s f t)
  𝒯₁s-comp leaf = refl
  𝒯₁s-comp (node _ t) = cong (node _) (ext-≅ (λ _ → 𝒯₁s-comp _))

  subst-𝒯₁s-comp : ∀ t → Path (𝒯₁s (g ∘C f) t) → Path (𝒯₁s g (𝒯₁s f t))
  subst-𝒯₁s-comp leaf p = p
  subst-𝒯₁s-comp (node _ _) (step _ p) = step _ (subst-𝒯₁s-comp _ p)

  subst-𝒯₁s-comp-≅ : ∀ t p → subst-𝒯₁s-comp t p ≅ p
  subst-𝒯₁s-comp-≅ leaf p = refl
  subst-𝒯₁s-comp-≅ (node _ t) (step _ p) = cong₂ step (ext-≅ (λ _ → sym (𝒯₁s-comp (t _)))) (subst-𝒯₁s-comp-≅ _ p)

  𝒯₁p-comp : ∀ t (p : Path (𝒯₁s (g ∘C f) t)) → 𝒯₁p (g ∘C f) _ p ≅ 𝒯₁p f _ (𝒯₁p g _ (subst-𝒯₁s-comp _ p))
  𝒯₁p-comp leaf p = refl
  𝒯₁p-comp (node _ t) (step _ p) = cong (step t) (𝒯₁p-comp _ p)

  𝒯₁-comp : 𝒯₁ (g ∘C f) ≡ 𝒯₁ g ∘C 𝒯₁ f
  𝒯₁-comp = 𝒯₁s-comp ⊲-≡' λ _ eq → trans (𝒯₁p-comp _ _) (cong _ (trans (subst-𝒯₁s-comp-≅ _ _) eq))


-- UNITALITY

graft-id : (t : Tree S P) → graft t (λ _ → leaf) ≅ t
graft-id leaf = refl
graft-id (node s t) = cong (node s) (ext-≅ (graft-id ∘ t))

pfst-id : ∀ (t : Tree S P) p → pfst {t = t} {f = λ _ → leaf} p ≅ p
pfst-id leaf stop = refl
pfst-id (node s t) (step _ p) = cong₂ step (sym (ext-≅ (graft-id ∘ t))) (pfst-id (t _) p)

η-μ-s : ∀ t → μs (sf (η (𝒯 C)) t) ≅ t
η-μ-s leaf = refl
η-μ-s (node _ t) = cong (node _) (ext-≅ (λ _ → graft-id _))

η-μ-p : ∀ t (p : Path (μs (sf (η (𝒯 C)) t))) → pf (η (𝒯 C)) t (μp _ p) ≅ p
η-μ-p leaf stop = refl
η-μ-p {C = C} (node s x) (step t p) = cong₂ step (ext-≅ (λ _ → sym (graft-id _))) (pfst-id _ _)

η-μ : μ ∘C η (𝒯 C) ≡ idC
η-μ = η-μ-s ⊲-≡' λ _ → trans (η-μ-p _ _)

η-μ-s' : ∀ t → μs (𝒯₁s (η C) t) ≅ t
η-μ-s' leaf = refl
η-μ-s' (node s x) = cong (node s) (ext-≅ (λ _ → η-μ-s' _))

η-μ-p' : ∀ t (p : Path (μs (𝒯₁s (η C) t))) → 𝒯₁p (η C) t (μp _ p) ≅ p
η-μ-p' leaf stop = refl
η-μ-p' (node s x) (step t p) = cong₂ step (ext-≅ (λ _ → sym (η-μ-s' _))) (η-μ-p' _ _)

η-μ' : μ ∘C 𝒯₁ (η C) ≡ idC
η-μ' = η-μ-s' ⊲-≡' λ _ → trans (η-μ-p' _ _)


-- ASSOCIATIVITY

data FreePath (S : Set) (P : S → Set) : Set where
  stop : FreePath S P
  step : ∀ s → P s → FreePath S P → FreePath S P

_++_ : FreePath S P → FreePath S P → FreePath S P
stop ++ q = q
step s r p ++ q = step s r (p ++ q)

++-assoc : (p q r : FreePath S P) → (p ++ q) ++ r ≅ p ++ (q ++ r)
++-assoc stop q r = refl
++-assoc (step _ _ p) q r = cong (step _ _) (++-assoc p q r)

p→fp : {t : Tree S P} → Path t → FreePath S P
p→fp {t = leaf} stop = stop
p→fp {t = node s _} (step {p = p} _ q) = step s p (p→fp q)

p2→fp : {t : Tree (Tree S P) Path} → Path t → FreePath S P
p2→fp {t = leaf} stop = stop
p2→fp {t = node s t} (step {p = p} _ q) = p→fp p ++ p2→fp q

p3→fp : {t : Tree (Tree (Tree S P) Path) Path} → Path t → FreePath S P
p3→fp {t = leaf} stop = stop
p3→fp {t = node s t} (step {p = p} _ q) = p2→fp p ++ p3→fp q

p→fp-inj : {p p' : Path t} → p→fp p ≅ p→fp p' → p ≅ p'
p→fp-inj {p = stop} {stop} eq = refl
p→fp-inj {p = step _ p} {step _ p'} eq
  with p→fp p in u | p→fp p' in v
... | _ | _ with refl ← eq = cong _ (p→fp-inj (≡-to-≅ (≡-trans u (≡-sym v))))

++≅++ : ∀ (p p' : FreePath S P) {q q'} → p ++ q ≅ p' ++ q' →
        Σ[ r ∈ FreePath S P ] p ≅ p' ++ r ⊎ Σ[ r ∈ FreePath S P ] p' ≅ p ++ r
++≅++ stop p' eq = inj₂ (_ , refl)
++≅++ (step _ _ p) stop eq = inj₁ (_ , refl)
++≅++ (step _ _ p) (step _ _ p') {q} {q'} eq
  with p ++ q in u | p' ++ q' in v
... | _ | _ with refl ← eq with ++≅++ p p' (≡-to-≅ (≡-trans u (≡-sym v)))
...   | inj₁ (r , refl) = inj₁ (r , refl)
...   | inj₂ (r , refl) = inj₂ (r , refl)

p→fp++ : {t : Tree S P} (p p' : Path t) {r : FreePath S P} → p→fp p ≅ p→fp p' ++ r → p→fp p ≅ p→fp p'
p→fp++ stop stop eq = refl
p→fp++ (step _ p) (step _ p') {r} eq
  with p→fp p in u | p→fp p' ++ r in v
... | _ | _ with refl ← eq = cong (step _ _) (trans (sym (≡-to-≅ u)) (p→fp++ _ _ (≡-to-≅ (≡-trans u (≡-sym v)))))

++-identity : (p : FreePath S P) → p ++ stop ≅ p
++-identity stop = refl
++-identity (step _ _ p) = cong (step _ _) (++-identity p)

++-inj : ∀ (p p' : FreePath S P) {q q'} → p ++ q ≅ p' ++ q' → p ≅ p' → q ≅ q'
++-inj stop stop eq eq' = eq
++-inj (step s x p) (step s₁ x₁ p') {q} {q'} eq refl
  with p ++ q in u | p ++ q' in v
... | _ | _ with refl ← eq = ++-inj p p' (≡-to-≅ (≡-trans u (≡-sym v))) refl

p2→fp++ : {t : Tree (Tree S P) Path} (p p' : Path t) {r : FreePath S P} → p2→fp p ≅ p2→fp p' ++ r → p2→fp p ≅ p2→fp p'
p2→fp++ stop stop eq = refl
p2→fp++ (step {p = p} _ q) (step {p = p'} _ q') eq
  with ++≅++ (p→fp p) (p→fp p') (trans eq (++-assoc (p→fp p') _ _))
... | inj₁ (_ , t) with refl ← p→fp-inj (p→fp++ _ _ t) = cong (_ ++_) (p2→fp++ q q' (++-inj _ _ (trans eq (++-assoc (p→fp p) _ _)) refl))
... | inj₂ (_ , t) with refl ← p→fp-inj (p→fp++ _ _ t) = cong (_ ++_) (p2→fp++ q q' (++-inj _ _ (trans eq (++-assoc (p→fp p) _ _)) refl))

p2→fp-inj : {t : Tree (Tree S P) Path} {p p' : Path t} → p2→fp p ≅ p2→fp p' → p ≅ p'
p2→fp-inj {p = stop} {stop} eq = refl
p2→fp-inj {p = step {p = p} _ q} {step {p = p'} _ q'} eq
  with ++≅++ (p→fp p) (p→fp p') eq
... | inj₁ (_ , t) with refl ← p→fp-inj (p→fp++ _ _ t) = cong _ (p2→fp-inj {p = q} (++-inj _ _ eq refl))
... | inj₂ (_ , t) with refl ← p→fp-inj (p→fp++ _ _ t) = cong _ (p2→fp-inj {p = q} (++-inj _ _ eq refl))

p3→fp-inj : {t : Tree (Tree (Tree S P) Path) Path} {p p' : Path t} → p3→fp p ≅ p3→fp p' → p ≅ p'
p3→fp-inj {p = stop} {stop} eq = refl
p3→fp-inj {p = step {p = p} _ q} {step {p = p'} _ q'} eq
  with ++≅++ (p2→fp p) (p2→fp p') eq
... | inj₁ (_ , t) with refl ← p2→fp-inj {p = p} (p2→fp++ p p' t) = cong _ (p3→fp-inj {p = q} (++-inj _ _ eq refl))
... | inj₂ (_ , t) with refl ← p2→fp-inj {p = p'} (p2→fp++ p' p t) = cong _ (p3→fp-inj {p = q} (++-inj _ _ eq refl))

graft++ : ∀ (t : Tree S P) v (p : Path (graft t v)) → p→fp p ≅ p→fp (pfst {t = t} p) ++ p→fp (psnd {t = t} p)
graft++ leaf v p = refl
graft++ (node _ t) v (step _ q) = cong (step _ _) (graft++ (t _) _ q)

graft2++ : ∀ (t : Tree (Tree S P) Path) v (p : Path (graft t v)) → p2→fp p ≅ p2→fp (pfst {t = t} p) ++ p2→fp (psnd {t = t} p)
graft2++ leaf v p = refl
graft2++ (node _ t) v (step {p = p} _ q) = trans (cong (_ ++_) (graft2++ (t _) _ _)) (sym (++-assoc (p→fp p) _ _))

p2→fp-μp : (p : Path (μs t)) → p→fp p ≅ p2→fp (μp t p)
p2→fp-μp {t = leaf} stop = refl
p2→fp-μp {t = node t x} p = trans (graft++ t _ p) (cong (p→fp (pfst p) ++_) (p2→fp-μp {t = x _} (psnd {t = t} p)))

p3→fp-μp : {t : Tree (Tree (Tree S P) Path) Path} (p : Path (μs t)) → p2→fp p ≅ p3→fp (μp t p)
p3→fp-μp {t = leaf} stop = refl
p3→fp-μp {t = node t x} p = trans (graft2++ t _ p) (cong (p2→fp (pfst {t = t} p) ++_) (p3→fp-μp {t = x _} (psnd {t = t} p)))

p3→fp-𝒯₁p : (p : Path (𝒯₁s μ t)) → p2→fp p ≅ p3→fp (𝒯₁p μ t p)
p3→fp-𝒯₁p {t = leaf} stop = refl
p3→fp-𝒯₁p {t = node s t} (step {p = p} _ q) = cong₂ _++_ (p2→fp-μp {t = s} p) (p3→fp-𝒯₁p q)

graft-assoc : (v : Path t → Tree _ _)
              (w : ∀ {p} → Path (v p) → Tree _ _) →
              ---------------------------------------
              graft t (λ p → graft (v p) w)
              ≅
              graft (graft t v) (λ q → w (psnd {f = v} q))

graft-assoc {t = leaf} v w = refl
graft-assoc {t = node s t} v w = cong (node s) (ext-≅ (λ p → graft-assoc {t = t p} _ _))

μs-graft-comm : ∀ (t : Tree (Tree S P) Path) v →
                ---------------------------
                μs (graft t v)
                ≅
                graft (μs t) (μs ∘ v ∘ μp _)

μs-graft-comm leaf v = refl
μs-graft-comm (node _ t) v = trans (cong (graft _) (ext-≅ (λ z → μs-graft-comm (t z) _))) (graft-assoc (μs ∘ t) _)

μs-assoc : (t : Tree (Tree (Tree S P) Path) Path) → μs (μs t) ≅ μs (𝒯₁s μ t)
μs-assoc leaf = refl
μs-assoc (node s t) = trans (μs-graft-comm s _) (cong (graft (μs s)) (ext-≅ (λ _ → μs-assoc (t _))))

p→fp≅ : {t t' : Tree S P} {p : Path t} {p' : Path t'} → t ≅ t' → p ≅ p' → p→fp p ≅ p→fp p'
p→fp≅ refl eq = cong p→fp eq

μp-assoc : {p : Path (μs (μs t))} {p' : Path (μs (𝒯₁s μ t))} →
           p ≅ p' →
           -----------------------------------
           𝒯₁p μ t (μp _ p')
           ≅
           μp t (μp _ p)

μp-assoc {t = t} {p} {p'} eq =
  p3→fp-inj (trans
    (sym (trans (p2→fp-μp {t = 𝒯₁s μ t} p') (p3→fp-𝒯₁p (μp (𝒯₁s μ t) p'))))
    (trans (p→fp≅ (sym (μs-assoc t)) (sym eq))
    (trans (p2→fp-μp {t = μs t} p) (p3→fp-μp {t = t} (μp _ p)))))

μ-assoc : μ ∘C μ ≡ μ {C} ∘C (𝒯₁ μ)
μ-assoc = μs-assoc ⊲-≡' λ _ → sym ∘ μp-assoc


-- NATURALITY OF MULTIPLICATION

𝒯₁s-graft-comm : ∀ (f : C ⇒ D) t v →
                 ---------------------------
                 𝒯₁s f (graft t v)
                 ≅ 
                 graft (𝒯₁s f t) (𝒯₁s f ∘ v ∘ 𝒯₁p f _)

𝒯₁s-graft-comm f leaf v = refl
𝒯₁s-graft-comm f (node _ t) v = cong (node _) (ext-≅ (λ _ → 𝒯₁s-graft-comm f (t _) _))

μs-natural : (f : C ⇒ D) → ∀ t → 𝒯₁s f (μs t) ≅ μs (𝒯₁s (𝒯₁ f) t)
μs-natural f leaf = refl
μs-natural f (node s t) = trans (𝒯₁s-graft-comm f s _) (cong (graft (𝒯₁s f s)) (ext-≅ (λ _ → μs-natural f (t _))))

subst-𝒯₁ : ∀ (f : C ⇒ D) t v →
           Path (𝒯₁s f (graft t v)) →
           Path (graft (𝒯₁s f t) (𝒯₁s f ∘ v ∘ 𝒯₁p f _))
subst-𝒯₁ f leaf v p = p
subst-𝒯₁ f (node s t) v (step _ q) = step _ (subst-𝒯₁ f (t _) _ q)

subst-𝒯₁-≅ : ∀ (f : C ⇒ D) t v p → subst-𝒯₁ f t v p ≅ p
subst-𝒯₁-≅ f leaf v p = refl
subst-𝒯₁-≅ f (node _ t) v (step _ p) = cong₂ {C = λ _ _ → Path _} step (ext-≅ (λ _ → sym (𝒯₁s-graft-comm f (t _) _))) (subst-𝒯₁-≅ f _ _ p)

μp-pfst : ∀ (f : C ⇒ D) t v →
          (p : Path (𝒯₁s f (graft t v))) →
          ------------------------------------
          pfst {t = t} (𝒯₁p f _ p)
          ≅
          𝒯₁p f _ (pfst {t = 𝒯₁s f t} (subst-𝒯₁ f t v p))

μp-pfst f leaf v p = refl
μp-pfst f (node _ t) v (step _ p) = cong (step t) (μp-pfst f (t _) _ p)

μp-psnd : ∀ (f : C ⇒ D) t v →
          (p : Path (𝒯₁s f (graft t v))) →
          -----------------------------------
          psnd {t = t} (𝒯₁p f _ p)
          ≅
          𝒯₁p f _ (psnd {t = 𝒯₁s f t} (subst-𝒯₁ f t v p))
          
μp-psnd f leaf v p = refl
μp-psnd f (node _ t) v (step _ p) = μp-psnd f (t _) _ p

subst-𝒯₁s-μs : (f : C ⇒ D) → ∀ t → Path (𝒯₁s f (μs t)) → Path (μs (𝒯₁s (𝒯₁ f) t))
subst-𝒯₁s-μs f leaf p = p
subst-𝒯₁s-μs f (node s t) p = ppair (pfst {t = 𝒯₁s f s} (subst-𝒯₁ f s _ p)) (subst-𝒯₁s-μs f (t _) (psnd {t = 𝒯₁s f s} (subst-𝒯₁ f s _ p)))

subst-𝒯₁s-μs-≅ : (f : C ⇒ D) → ∀ t p → subst-𝒯₁s-μs f t p ≅ p
subst-𝒯₁s-μs-≅ f leaf p = refl
subst-𝒯₁s-μs-≅ f (node s t) p =
  trans
    (graft-eq {t = 𝒯₁s f s} _ _
      (ext-≅ (λ _ → sym (μs-natural f (t _))))
      (pfst-ppair _ _)
      (trans (psnd-ppair {t = 𝒯₁s f s} _ _) (subst-𝒯₁s-μs-≅ f (t _) _)))
    (subst-𝒯₁-≅ f _ _ p)

μp-natural : (f : C ⇒ D) → ∀ t →
             (p : Path (𝒯₁s f (μs t))) →
             -------------------------------
             μp t (𝒯₁p f _ p)
             ≅
             𝒯₁p _ _ (μp (𝒯₁s _ t) (subst-𝒯₁s-μs f t p))

μp-natural f leaf p = refl
μp-natural f (node s t) p = cong₂ (λ z → step {p = z} t)
  (trans (μp-pfst f _ _ p) (cong (𝒯₁p f s) (sym (pfst-ppair _ _))))
  (trans
    (trans
      (cong₂ (μp ∘ t) (μp-pfst f _ _ p) (μp-psnd f s _ p))
      (μp-natural f (t _) (psnd {t = sf (𝒯₁ f) s} (subst-𝒯₁ f s _ p))))
    (cong₂ (𝒯₁p (𝒯₁ f))
      (cong (λ z → t (𝒯₁p f _ z)) (sym (pfst-ppair _ _)))
      (cong₂ (λ z → μp (𝒯₁s (𝒯₁ f) (t (𝒯₁p f s z)))) (sym (pfst-ppair _ _)) (sym (psnd-ppair {t = 𝒯₁s f s} _ _)))))

μ-natural : (f : C ⇒ D) → 𝒯₁ f ∘C μ ≡ μ ∘C 𝒯₁ (𝒯₁ f)
μ-natural f = μs-natural f ⊲-≡' λ s eq → trans (μp-natural _ _ _) (cong _ (trans (subst-𝒯₁s-μs-≅ f s _) eq))


-- NATURALITY OF UNIT

η-natural : (f : C ⇒ D) → 𝒯₁ f ∘C η C ≡ η D ∘C f
η-natural f = (λ _ → refl) ⊲-≡' λ {_ {p = step _ _} refl → refl}


-- TREE MONAD

TreeMonad : Monad Cont
TreeMonad = record
  { F = record
    { F₀ = 𝒯
    ; F₁ = 𝒯₁
    ; identity = 𝒯₁-id
    ; homomorphism = 𝒯₁-comp _ _
    ; F-resp-≈ = λ {_≡_.refl → _≡_.refl}
    }
  ; η = record { η = η ; commute = λ f → ≡-sym (η-natural f) ; sym-commute = η-natural }
  ; μ = record { η = λ _ → μ ; commute = λ f → ≡-sym (μ-natural f) ; sym-commute = μ-natural }
  ; assoc = ≡-sym μ-assoc
  ; sym-assoc = μ-assoc
  ; identityˡ = η-μ'
  ; identityʳ = η-μ
  }