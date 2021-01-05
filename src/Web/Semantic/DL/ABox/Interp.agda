open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ) renaming 
  ( Interp to Interp′ ; emp to emp′ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( False ; id )

module Web.Semantic.DL.ABox.Interp where

infixr 4 _,_
infixr 5 _*_ 

{-
   An ABox interpretation of a signature Σ (made of concept and role names)
   over a set X of individuals consists of
    - a TBox interpreation I
    - a mapping from X do Δ I, the domain of interpretation of I
   Note: In RDF the members of X are  sets of IRIs, BNodes or Literals, but
   IRIs can also refer to TBox elements.
-}
data Interp (Σ : Signature) (X : Set) : Set₁ where
  -- I is a full Interpreation (Interp')
  -- The function X → Δ {Σ} I interprets the variables in X
  _,_ : ∀ I → (X → Δ {Σ} I) → (Interp Σ X)  

-- extract the Interpretation, forgetting the interpretation of variables
⌊_⌋ : ∀ {Σ X} → Interp Σ X → Interp′ Σ
⌊ I , i ⌋ = I

-- return the individuals function for an interpretation
ind : ∀ {Σ X} → (I : Interp Σ X) → X → Δ ⌊ I ⌋
ind (I , i) = i

-- paired individuals function for an interpretation, useful for relations/roles
ind² : ∀ {Σ X} → (I : Interp Σ X) → (X × X) → (Δ ⌊ I ⌋ × Δ ⌊ I ⌋)
ind² I (x , y) = (ind I x , ind I y)

-- why * ?
_*_ : ∀ {Σ X Y} → (Y → X) → Interp Σ X → Interp Σ Y
f * I = (⌊ I ⌋ , λ y → ind I (f y))

-- Empty interpretation
emp : ∀ {Σ} → Interp Σ False
emp = (emp′ , id)

data Surjective {Σ X} (I : Interp Σ X) : Set where
  -- y is a variable i.e. y : X 
  -- (ind I y), x : Δ
  -- all elements x of the domain Δ, have a variable y that it is an interpretation of   
  surj : (∀ x → ∃ λ y → ⌊ I ⌋ ⊨ x ≈ ind I y) → (I ∈ Surjective)

ind⁻¹ : ∀ {Σ X} {I : Interp Σ X} → (I ∈ Surjective) → (Δ ⌊ I ⌋ → X)
ind⁻¹ (surj i) x = proj₁ (i x)

surj✓ : ∀ {Σ X} {I : Interp Σ X} (I∈Surj : I ∈ Surjective) → ∀ x → (⌊ I ⌋ ⊨ x ≈ ind I (ind⁻¹ I∈Surj x))
surj✓ (surj i) x = proj₂ (i x)
