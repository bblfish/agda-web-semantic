open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )

module Web.Semantic.DL.KB where

infixr 4 _,_

{- A Knowledge Base over a signature and variables/names X
  consists of a TBox and an ABox -}
data KB (Σ : Signature) (X : Set) : Set where
  _,_ : (T : TBox Σ) → (A : ABox Σ X) → KB Σ X

tbox : ∀ {Σ X} → KB Σ X → TBox Σ
tbox (T , A) = T

abox : ∀ {Σ X} → KB Σ X → ABox Σ X
abox (T , A) = A
