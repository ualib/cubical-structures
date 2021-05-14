---
layout: default
title : structures.basic module
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

open import Agda.Primitive renaming (lzero to ℓ₀) using (lsuc; _⊔_)
open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax; fst; snd)
open import Cubical.Data.Sigma using (_,_; _×_)
open import Cubical.Relation.Binary.Base renaming (Rel to REL) using ()
open import relations.discrete renaming (Rel to BinRel) using (_|:_)

open import overture.preliminaries using (∣_∣; ∥_∥)

module structures.basic where

variable
 α β 𝓤 : Level

ℓ₁ : Level  -- (alias)
ℓ₁ = lsuc ℓ₀

Arity : Type ℓ₁
Arity = Type ℓ₀   -- (assuming all arity types have universe level 0)

{-Op is the type of (interpreted) operations.
  @param a : Type 0 is the operation's arity
  @param B : Type (lsuc 𝓤) is the operations's domain -}
Op : Arity → Type 𝓤 → Type 𝓤
Op a B = (a → B) → B

Rel : Arity → Type 𝓤 → Type (lsuc 𝓤)
Rel {𝓤} a B = (a → B) → Type 𝓤

-- Inhabitants of Signature type are pairs, (s , ar), where s is an operation or
-- relation symbol and ar its arity.
Signature : Type ℓ₁
Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity)

Structure : (𝑅 𝐹 : Signature){β : Level} → Type (lsuc β)
Structure 𝑅 𝐹 {β} =
 Σ[ B ∈ Type β ]                    -- the domain of the structure is B
  ( ((r : ∣ 𝑅 ∣) → Rel(∥ 𝑅 ∥ r) B)  -- the interpretations of the relation symbols
  × ((f : ∣ 𝐹 ∣) → Op(∥ 𝐹 ∥ f) B) ) -- the interpretations of the operation symbols

RStructure : (β : Level) → Signature → Type (lsuc β)
RStructure β 𝑅 = Σ[ B ∈ Type β ] ∀(r : ∣ 𝑅 ∣) → Rel(∥ 𝑅 ∥ r) B

AStructure : (β : Level) → Signature → Type (lsuc β)
AStructure β 𝐹 = Σ[ B ∈ Type β ] ∀ (f : ∣ 𝐹 ∣) → Op (∥ 𝐹 ∥ f) B

-- Reducts
Structure→AStructure : {𝑅 𝐹 : Signature}{β : Level} → Structure 𝑅 𝐹 → AStructure β 𝐹
Structure→AStructure (B , (ℛ , ℱ)) = B , ℱ

Structure→RStructure : {𝑅 𝐹 : Signature}{β : Level} → Structure 𝑅 𝐹 → RStructure β 𝑅
Structure→RStructure (B , (ℛ , ℱ)) = B , ℛ


module _ {𝑅 𝐹 : Signature}  where
{- Let 𝑅 and 𝐹 be signatures and let ℬ = (B , (ℛ , ℱ)) be an (𝑅, 𝐹)-structure.
   - If `r : ∣ 𝑅 ∣` is a relation symbol, then `rel ℬ r` is the interpretation of `r` in `ℬ`.
   - if `f : ∣ 𝐹 ∣` is an opereation symbol, then `op ℬ f` is the interpretation
   of `f` in `ℬ`. -}

  -- Syntax for interpretation of relations and operations.
  _⟦_⟧ᵣ : (ℬ : Structure 𝑅 𝐹 {β})(R : fst 𝑅) → Rel ((snd 𝑅) R) (fst ℬ)
  ℬ ⟦ R ⟧ᵣ = λ b → (∣ snd ℬ ∣ R) b

  _⟦_⟧ₒ : (ℬ : Structure 𝑅 𝐹 {β})(𝑓 : fst 𝐹) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  ℬ ⟦ 𝑓 ⟧ₒ = λ b → (snd (snd ℬ) 𝑓) b

  _ʳ_ : (R : fst 𝑅)(ℬ : Structure 𝑅 _ {β}) → Rel ((snd 𝑅) R) (fst ℬ)
  R ʳ ℬ = λ b → (ℬ ⟦ R ⟧ᵣ) b

  _ᵒ_ : (𝑓 : fst 𝐹)(ℬ : Structure _ 𝐹 {β}) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  𝑓 ᵒ ℬ = λ b → (ℬ ⟦ 𝑓 ⟧ₒ) b

  compatible : (𝑩 : Structure 𝑅 𝐹 {β}) → BinRel (fst 𝑩) α  → Type (β ⊔ α)
  compatible 𝑩 r = ∀ 𝑓 → (𝑓 ᵒ 𝑩) |: r



-- Alternative development using records

record signature : Type ℓ₁ where
 field
  symbol : Type ℓ₀
  ar : symbol → Arity

open signature


record structure (𝑅 𝐹 : signature) {β : Level} : Type (lsuc β) where
 field
  univ : Type β
  rel  : ∀ (r : symbol 𝑅) → Rel(ar 𝑅 r) univ  -- interpretations of relations
  op   : ∀ (f : symbol 𝐹) → Op (ar 𝐹 f) univ  -- interpretations of operations

open structure

compatible' : {𝑅 𝐹 : signature}{β : Level}(𝑩 : structure 𝑅 𝐹 {β}){α : Level} → BinRel (univ 𝑩) α  → Type (α ⊔ β)
compatible' {𝑅}{𝐹} 𝑩 r = ∀ (𝑓 : symbol 𝐹)(u v : (ar 𝐹) 𝑓 → univ 𝑩) → ((op 𝑩) 𝑓) |: r




\end{code}


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------





































<!--  NO LONGER USED ---------------------------------------------------

  -- _⟦_⟧ᵣ : {β : Level}(ℬ : Structure 𝑅 _ {β})(R : fst 𝑅) → Rel ((snd 𝑅) R) (fst ℬ)
  -- ℬ ⟦ R ⟧ᵣ = λ b → (rel ℬ R) b

  -- _⟦_⟧ₒ : {β : Level}(ℬ : Structure _ 𝐹 {β})(𝑓 : fst 𝐹) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  -- ℬ ⟦ 𝑓 ⟧ₒ = λ b → (op ℬ 𝑓) b

  -- _ʳ_ : {β : Level}(R : fst 𝑅)(ℬ : Structure 𝑅 _ {β}) → Rel ((snd 𝑅) R) (fst ℬ)
  -- R ʳ ℬ = λ b → (rel ℬ R) b

  -- _ᵒ_ : {β : Level}(𝑓 : fst 𝐹)(ℬ : Structure _ 𝐹 {β}) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  -- 𝑓 ᵒ ℬ = λ b → (op ℬ 𝑓) b



We now define the function `compatible` so that, if `𝑩` denotes a structure and
`r` a binary relation, then `compatible 𝑩 r` will represent the assertion that
`r` is *compatible* with all basic operations of `𝑩`. in the following sense:

```
 ∀ 𝑓 : ∣ 𝐹 ∣ → ∀ (x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣)
            →  (∀ i → r (x i) (y i)) → r (f x) (f y)
```

The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

eval-rel : {β ℓ : Level}{B : Type β}{I : Arity} → BinRel B ℓ → BinRel (I → B) ℓ
eval-rel r u v = ∀ i → r (u i) (v i)

_|:_ : {β ℓ : Level}{B : Type β}{I : Arity} → Op I B → BinRel B ℓ → Type (β ⊔ ℓ)
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}












-- data Kind : Type ℓ₀ where
--  relation : Kind
--  operation : Kind

-- Relation symbol types and operation symbol types live in universe level lzero.
-- Signature : Type (lsuc lzero)
-- Signature = Σ[ F ꞉ Type₀ ] (F → Kind × Arity)

 -- interpret : Kind × Arity → Type (lsuc 𝓤) → Type (lsuc 𝓤)
 -- interpret (relation , a) B = Rel a B
 -- interpret (operation , a) B = Op a B
-- (((r : ∣ 𝑅 ∣) → Re (∥ 𝑅 ∥ r) A)    -- the basic relations
--                   + ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A))     -- the basic operations


-- module _ {𝑅 : relsig σ α}{𝑆 : algsig σ α} where

--  _̇_ : (𝑓 : Symbol 𝑆)(𝑨 : Structure 𝓤 𝑅 𝑆) → ?

--  relsym a = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎

-- \end{code}

--general signature
-- sig : (σ αr αo : Level) → Type (lsuc (αr ⊔ αo ⊔ σ))
-- sig σ αr αo = (Σ[ s ꞉ Type σ ] (s → ((Type αr × Level) + Type αo)))
-- sig : (α 𝓤 : Level) → Type (lsuc (αr ⊔ αo ⊔ σ))
-- sig α 𝓤 = (Σ[ s ꞉ sigsym α 𝓤 ] λ { relsym a B → inj₁ (a , B)Type αr × Level) + Type αo)))

--Example: the signature of structures with one binary relation symbol, and two operation symbols, one nullary and one unary (so, a magma with an extra binary relation).

-- data rmagma {σ : Level} : Type σ where
--  _-̇_ : rmagma  -- binary relation symbol
--  𝟏 : rmagma    -- nullary operation symbol
--  ⊡ : rmagma    -- binary operation symbol
-- open rmagma
-- rmagma-sig : {σ : Level} → sig σ lzero lzero
-- rmagma-sig = rmagma ,
--              λ { _-̇_ → inj₁ ((⊤ + ⊤) , lzero)  -- binary relation arity (2)
--                ; 𝟏 → inj₂ ⊥                    -- nullary operation arity (0)
--                ; ⊡ → inj₂ (⊤ + ⊤)              -- binary operation airty (2)
--                }




-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.HalfAdjoint
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.SIP
-- open import Cubical.Displayed.Base
-- open import Cubical.Displayed.Auto
-- open import Cubical.Displayed.Record
-- open import Cubical.Displayed.Universe
-- -- open import Agda.Builtin.Bool
-- open import Agda.Builtin.Unit using (⊤)
-- open import Data.Empty using (⊥)
-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
-- open import Data.Sum.Base renaming (_⊎_ to _+_) using ()
-- open import overture.preliminaries using (∣_∣; ∥_∥) -- ; snd; fst) -- ; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; -Σ) -- Type; Type₀; -Σ; 
-- open import relations.discrete using (_|:_)


----------------------------------------------------------------------- -->
