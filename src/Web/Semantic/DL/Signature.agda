module Web.Semantic.DL.Signature where

infixr 4 _,_

-- a Signature is constructed from Concept Names and Role/Relation Names
data Signature : Set₁ where
  _,_ : (CN RN : Set) → Signature

-- concept name (maps to Sets)
CN : Signature → Set
CN (CN , RN) = CN

-- Role Names (or relation names)
RN : Signature → Set
RN (CN , RN) = RN
