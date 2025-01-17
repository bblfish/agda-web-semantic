open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Concept using ( Concept )
open import Web.Semantic.DL.Role using ( Role )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.TBox where

infixl 5 _⊑₁_ _⊑₂_
infixr 4 _,_

{- a Terminology Box on a Signature (Concept and Role Names)
  is constructed by specifying
   - ε the empty TBox
   - Combination of TBoxes (_,_) - ie. a Union
   - subsumption relations ⊑ between roles and between concepts 
   - properties of Roles (Reflexivity, Irreflexivity, Transitivity)
   - disjointness relation between Roles -}
data TBox (Σ : Signature) : Set where
  ε : TBox Σ 
  _,_ : (T U : TBox Σ) → TBox Σ
  _⊑₁_ : (C D : Concept Σ) → TBox Σ
  _⊑₂_ : (Q R : Role Σ) → TBox Σ
  Ref : (R : Role Σ) → TBox Σ
  Irr : (R : Role Σ) → TBox Σ
  Tra : (R : Role Σ) → TBox Σ
  Dis : (Q R : Role Σ) → TBox Σ

Axioms : ∀ {Σ} → TBox Σ → Subset (TBox Σ)
Axioms ε         = ∅
Axioms (T , U)   = (Axioms T) ∪ (Axioms U)
Axioms (C ⊑₁ D)  = ⁅ C ⊑₁ D ⁆
Axioms (Q ⊑₂ R)  = ⁅ Q ⊑₂ R ⁆
Axioms (Ref R)   = ⁅ Ref R ⁆
Axioms (Irr R)   = ⁅ Irr R ⁆
Axioms (Tra R)   = ⁅ Tra R ⁆
Axioms (Dis Q R) = ⁅ Dis Q R ⁆

