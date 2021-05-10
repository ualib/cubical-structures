---
layout: default
title : structures.basic module
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
-- open import Agda.Builtin.Bool
open import Agda.Builtin.Unit using (⊤)
open import Relation.Binary.Core renaming (Rel to BinRel) using (_⇒_;_=[_]⇒_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Data.Sum.Base renaming (_⊎_ to _+_) using ()

open import overture.preliminaries using (Type; Type₀; -Σ; ∣_∣; ∥_∥; snd; fst) -- ; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; -Σ)

-- open import relations.discrete using (_|:_)

module structures.basic where

-- Aliases.
ℓ₀ ℓ₁ : Level
ℓ₀ = lzero
ℓ₁ = lsuc lzero


-- All arity types will have universe level 0.
Arity : Type ℓ₁
Arity = Type ℓ₀

{- Op is the type of (interpreted) operations.
   @param 𝓤 : Level The universe level of the operation's domain is lsuc 𝓤
              (so operations and relations end up in the same codomain universe)
   @param a : Type 0 is the operation's arity
   @param B : Type (lsuc 𝓤) is the operations's domain -}
Op : {𝓤 : Level} → Arity → Type 𝓤 → Type 𝓤
Op a B = (a → B) → B

Rel : {𝓤 : Level} → Arity → Type 𝓤 → Type (𝓤 ⊔ ℓ₁)
Rel a B = (a → B) → Type ℓ₀

-- Inhabitants of the Symbol type are pairs, (s , ar), where s is a symbol and ar is its arity. 




Signature : Type (lsuc lzero)
Signature = Σ[ F ꞉ Type ℓ₀ ] (F → Arity)


-- Inhabitants of Sigature type are triples (s , k , a), where s is the symbol, k is the symbol kind (i.e., relation or operation), and a is the arity.


open _+_

ℛ : {β : Level} → Signature → Type β → Type (β ⊔ ℓ₁)
ℛ 𝑆 B = ∀ (r : ∣ 𝑆 ∣) → Rel (∥ 𝑆 ∥ r) B

ℱ : {β : Level} → Signature → Type β → Type β
ℱ 𝑆 B = ∀ (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) B

Structure : (β : Level) → (𝑅 𝐹 : Signature) → Type (lsuc β)
Structure β 𝑅 𝐹 = Σ[ B ꞉ Type β ] (ℛ 𝑅 B × ℱ 𝐹 B)

RStructure : (β : Level) → Signature → Type (lsuc β)
RStructure β 𝑅 = Σ[ B ꞉ Type β ] ℛ 𝑅 B

AStructure : (β : Level) → Signature → Type (lsuc β)
AStructure β 𝐹 = Σ[ B ꞉ Type β ] ℱ 𝐹 B

-- Reducts
Structure→AStructure : {β : Level} {𝑅 𝐹 : Signature} → Structure β 𝑅 𝐹 → AStructure β 𝐹
Structure→AStructure (B , (ℛ , ℱ)) = B , ℱ

Structure→RStructure : {β : Level} {𝑅 𝐹 : Signature} → Structure β 𝑅 𝐹 → RStructure β 𝑅
Structure→RStructure (B , (ℛ , ℱ)) = B , ℛ


module _ {β : Level}{𝑅 𝐹 : Signature}  where
  rel : ((B , (ℛ , ℱ)) : Structure β 𝑅 𝐹) → (r : ∣ 𝑅 ∣) → Rel (∥ 𝑅 ∥ r) B
  rel (_ , (ℛ , _)) = ℛ

  op : ((B , (ℛ , ℱ)) : Structure β 𝑅 𝐹) → (f : ∣ 𝐹 ∣) → Op (∥ 𝐹 ∥ f) B
  op (_ , (_ , ℱ)) = ℱ

{- Let 𝑅 and 𝐹 be signatures and let ℬ = (B , (ℛ , ℱ)) be an (𝑅, 𝐹)-structure.
   - If `r : ∣ 𝑅 ∣` is a relation symbol, then `rel ℬ r` is the interpretation of `r` in `ℬ`.
   - if `f : ∣ 𝐹 ∣` is an opereation symbol, then `op ℬ f` is the interpretation
   of `f` in `ℬ`. -}

  -- Syntax for interpretation of relations and operations.
  _⟦_⟧ᵣ : (ℬ : Structure β 𝑅 _)(R : ∣ 𝑅 ∣) → Rel (∥ 𝑅 ∥ R ) ∣ ℬ ∣
  ℬ ⟦ R ⟧ᵣ = λ b → (rel ℬ R) b

  _⟦_⟧ₒ : (ℬ : Structure β _ 𝐹)(𝑓 : ∣ 𝐹 ∣) → Op (∥ 𝐹 ∥ 𝑓 ) ∣ ℬ ∣
  ℬ ⟦ 𝑓 ⟧ₒ = λ b → (op ℬ 𝑓) b

  _ʳ_ : (R : ∣ 𝑅 ∣)(ℬ : Structure β 𝑅 _) → Rel (∥ 𝑅 ∥ R ) ∣ ℬ ∣
  R ʳ ℬ = λ b → (rel ℬ R) b

  _ᵒ_ : (𝑓 : ∣ 𝐹 ∣)(ℬ : Structure β _ 𝐹) → Op (∥ 𝐹 ∥ 𝑓 ) ∣ ℬ ∣
  𝑓 ᵒ ℬ = λ b → (op ℬ 𝑓) b



\end{code}




#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

We now define the function `compatible` so that, if `𝑩` denotes a structure and
`r` a binary relation, then `compatible 𝑩 r` will represent the assertion that
`r` is *compatible* with all basic operations of `𝑩`. in the following sense:

```
 ∀ 𝑓 : ∣ 𝐹 ∣ → ∀ (x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣)
            →  (∀ i → r (x i) (y i)) → r (f x) (f y)
```

The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

\begin{code}

eval-rel : {β ℓ : Level}{B : Type β}{I : Arity} → BinRel B ℓ → BinRel (I → B) ℓ
eval-rel r u v = ∀ i → r (u i) (v i)

_|:_ : {β ℓ : Level}{B : Type β}{I : Arity} → Op I B → BinRel B ℓ → Type (β ⊔ ℓ)
f |: R  = (eval-rel R) =[ f ]⇒ R


compatible : {β ℓ : Level}{𝑅 𝐹 : Signature}(𝑩 : Structure β 𝑅 𝐹) → BinRel ∣ 𝑩 ∣ ℓ  → Type (β ⊔ ℓ)
compatible 𝑩 r = ∀ 𝑓 → (𝑓 ᵒ 𝑩) |: r

\end{code}

compatible' : {β ℓ : Level}{𝑅 𝐹 : Signature}(𝑩 : Structure β 𝑅 𝐹)
 → ((I : Arity) → BinRel (I → ∣ 𝑩 ∣) ℓ)  → Type (β ⊔ ℓ)
compatible' {𝐹 = 𝐹} 𝑩 r = ∀ (𝑓 : ∣ 𝐹 ∣)(u v : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (r (∥ 𝐹 ∥ 𝑓)) u v →  (r ⊤ ) ((𝑓 ᵒ 𝑩) u) ((𝑓 ᵒ 𝑩) v)



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





\end{code}



--------------------------------------


{% include cubical-algebras.links.md %}
