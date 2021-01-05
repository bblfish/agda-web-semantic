open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( Finite )

module Web.Semantic.DL.Category.Object {Σ : Signature} where

infixr 4 _,_
{-
This Object represents a Knowledge Base (schema + facts) with constraints.
It is defined over two TBoxes on the same Signature Σ
  S is the standard TBox - i.e. a schema
  T is the consTraint TBox - constraints on the facts A below
It is built from  
  A is a  set of ABox facts over a finite set of variables

see "Integrity Constraints for Linked Data"
and especially the reference from there to Definition 1 p11 of
"Bridging the Gap between OWL and Relational Databases"
by Boris Motik, Ian Horrocks and Ulrike Sattler
-}
data Object (S T : TBox Σ) : Set₁ where
  _,_ : ∀ X → (X ∈ Finite × ABox Σ X) → Object S T

-- Interface Names, the nodes that can be used by other ABoxes
IN : ∀ {S T} → Object S T → Set
IN (X , X∈Fin , A) = X

-- the proof that X is finite 
fin : ∀ {S T} → (A : Object S T) → (IN A ∈ Finite)
fin (X , X∈Fin , A) = X∈Fin

{- An ABox thought of as an interface
 (language from  "§3 Initial Interpretation" of
 "Integrity Constraints for Linked Data" )
The idea is that an ABox either creates nodes
that can be used by others or it uses nodes from
other ABoxes, and so it provides an interface to others  -}
iface : ∀ {S T} → (A : Object S T) → (ABox Σ (IN A))
iface (X , X∈Fin , A) = A
