open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; ∅ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Setoid ; Subset ; _∘_ ; False )

module Web.Semantic.DL.TBox.Interp where

{- TBox interpretation of a Signature Σ
   consists essentially of:
     1. A Domain Δ of intepretation
     2. An equivalence relation on Δ
     3. An interpretation of Σ, i.e. a function from CN and RN to Δ
     4. Proofs that the interpretations respect the Equivalence Relation
   One would use records in Agda 2.6.x
 -}
data Interp (Σ : Signature) : Set₁ where
  interp :
    (Δ : Set) → -- The Domain of Interpretation (e.g. representing real objects in the world)
    (_≈_ : Δ → Δ → Set) →     -- an equivalence relation between those objects (one may have hesperus ≈ phosphorus)
    (ref : ∀ {x} → (x ≈ x)) →             -- proof of reflexivity of equivalence relation
    (sym : ∀ {x y} → (x ≈ y) → (y ≈ x)) → -- proof of symmetry of ≈
    (trans : ∀ {x y z} → (x ≈ y) → (y ≈ z) → (x ≈ z)) → -- proof of transitivity
    (con : CN Σ → Subset Δ) →             -- concept names of signature map
    (rol : RN Σ → Subset (Δ × Δ)) →       -- role name of signature map
    (con-≈ : ∀ {x y} c → (x ∈ con c) → (x ≈ y) → (y ∈ con c)) →
    (rol-≈ : ∀ {w x y z} r → (w ≈ x) → ((x , y) ∈ rol r) → (y ≈ z) → ((w , z) ∈ rol r)) →
    Interp Σ

{-
 the functions below return some elements of Interp,
 which would with Agda 2.6.* be given by the record structure
 -}

-- The Domain of Interpretation (e.g. representing real objects in the world) 
Δ : ∀ {Σ} → Interp Σ → Set
Δ (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = Δ

-- this semantic entailment relation is unusual as it relates an interpretation to 
-- elements in the domain whereas usually we have 
-- M ⊨ P where M is a model and P a sentence of the language (as done in Institution Theory)
-- so we might have I ⊨ { a owl:sameAs b }
-- which would be true if a refers to the same object as b in Δ via I
-- this may indicate a confusion of syntax with semantics here.
_⊨_≈_ : ∀ {Σ} → (I : Interp Σ) → (Δ I) → (Δ I) → Set
_⊨_≈_ (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = _≈_

≈-refl : ∀ {Σ} → (I : Interp Σ) → ∀ {x} → (I ⊨ x ≈ x)
≈-refl (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = ref

≈-sym : ∀ {Σ} → (I : Interp Σ) → ∀ {x y} → (I ⊨ x ≈ y) → (I ⊨ y ≈ x)
≈-sym (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = sym

≈-trans : ∀ {Σ} → (I : Interp Σ) → ∀ {x y z} → (I ⊨ x ≈ y) → (I ⊨ y ≈ z) → (I ⊨ x ≈ z)
≈-trans (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = trans

-- concept names of signature map
con : ∀ {Σ} → (I : Interp Σ) → CN Σ → Subset (Δ I)
con (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = con

-- role name of signature map
rol : ∀ {Σ} → (I : Interp Σ) → RN Σ → Subset (Δ I × Δ I)
rol (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = rol

con-≈ : ∀ {Σ} → (I : Interp Σ) → ∀ {x y} c → (x ∈ con I c) → (I ⊨ x ≈ y) → (y ∈ con I c)
con-≈ (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = con-≈

rol-≈ : ∀ {Σ} → (I : Interp Σ) → ∀ {w x y z} r → (I ⊨ w ≈ x) → ((x , y) ∈ rol I r) → (I ⊨ y ≈ z) → ((w , z) ∈ rol I r)
rol-≈ (interp Δ _≈_ ref sym trans con rol con-≈ rol-≈) = rol-≈

{-
 Additional functions
-}

-- Interpretation implies two elements are not equal
_⊨_≉_ : ∀ {Σ} → (I : Interp Σ) → (Δ I) → (Δ I) → Set
I ⊨ x ≉ y = ¬(I ⊨ x ≈ y)

-- the Empty Interpretation
emp : ∀ {Σ} → Interp Σ
emp = interp False (λ ()) (λ {}) (λ {}) (λ {}) (λ c → ∅) (λ r → ∅) (λ {}) (λ {})

-- relf implies ≈
≈-refl′ : ∀ {Σ} (I : Interp Σ) → ∀ {x y} → (x ≡ y) → (I ⊨ x ≈ y)
≈-refl′ I refl = ≈-refl I
