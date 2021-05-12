---
layout: default
title : relations.discrete module
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}


-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_)
open import Function.Base using (_on_)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; _,_; Σ-syntax)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base renaming (Rel to REL) using ()
open import Cubical.Data.Sigma using (_×_)


open import overture.preliminaries using (𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩)

module relations.discrete where


-- The binary relation type `Rel` in Cubical.Relation.Binary.Base is the more general
-- (heterogeneous) binary relation so we rename it `REL` and use Rel for the homomgeneous
-- binary relation (like in the standard library).  (This just saves us from having to repeat
-- the domain type of homogeneous relations.)
--
-- Heterogeneous binary relation type (imported from Cubical.Relation.Binary.Base)
-- REL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
-- REL A B ℓ' = A → B → Type ℓ'

-- Homogeneous binary relation type
Rel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
Rel A ℓ' = REL A A ℓ'





Im_⊆_ : {A : Type 𝓤}{B : Type 𝓦} → (A → B) → Pred B 𝓩 → Type (𝓤 ⊔ 𝓩)
Im f ⊆ S = ∀ x → f x ∈ S


module _ {A : Type 𝓤}{B : Type 𝓦} where

 ker : (A → B) → Rel A 𝓦
 ker g x y = g x ≡ g y

 ker' : (A → B) → (I : Type 𝓥) → Rel (I → A) (𝓦 ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) 𝓦
 kernel g (x , y) = g x ≡ g y


module _ {A : Type 𝓤 } where

 𝟎 : Rel A 𝓤
 𝟎 x y = x ≡ y

 𝟎-pred : Pred (A × A) 𝓤
 𝟎-pred (x , y) = x ≡ y

 𝟎-sigma : Type 𝓤
 𝟎-sigma = Σ[ x ∈ A ] Σ[ y ∈ A ] x ≡ y

 𝟎-sigma' : Type 𝓤
 𝟎-sigma' = Σ[ (x , y) ∈ A × A ] x ≡ y

--The type of operations
Op : Type 𝓥 → Type 𝓤 → Type(𝓤 ⊔ 𝓥)
Op I A = (I → A) → A

π : {I : Type 𝓥 } {A : Type 𝓤 } → I → Op I A
π i x = x i



{- -- Compatibility of binary relations --

   We now define the function `compatible` so that, if `𝑩` denotes a structure and `r` a
   binary relation, then `compatible 𝑩 r` will represent the assertion that `r` is *compatible*
   with all basic operations of `𝑩`. in the following sense:
   `∀ 𝑓 : ∣ 𝐹 ∣ → ∀(x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (∀ i → r (x i)(y i)) → r (f x)(f y)`
-}


eval-rel : {A : Type 𝓤}{I : Type 𝓥} → Rel A 𝓦 → Rel (I → A)(𝓥 ⊔ 𝓦)
eval-rel R u v = ∀ i → R (u i) (v i)

compatible-op : {A : Type 𝓤}{I : Type 𝓥} → Op I A → Rel A 𝓦 → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)


-- Fancy notation for compatible-op -------------------------

-- Omitting `Relation.Binary.Core using (REL; Rel; _⇒_;_=[_]⇒_)`
-- since we redefine _⇒_ and _=[_]⇒_ to be sure it's compatible with Cubical.
-- Note to self: have a look at module Cubical.Functions.Logic when we have a
-- chance. Maybe there's something there we can use instead.


-- NOTE: `_⇒_`, `_=[_]⇒_` and `_Preserves_⟶_` are lifted from
--   `Relation.Binary.Core`  (modulo minor syntax mods)

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b


infix 4 _⇒_ _=[_]⇒_

_⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Type _
P ⇒ Q = ∀ {x y} → P x y → Q x y

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Type _
P =[ f ]⇒ Q = P ⇒ (Q on f)


_|:_ : {I : Type 𝓥} → Op I A → Rel A 𝓦 → Type _
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}



--------------------------------------


{% include cubical-algebras.links.md %}
















<!-- No longer needed -------------------------------

-- open import Agda.Builtin.Equality using (_≡_)
-- open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
-- open import Data.Empty using (⊥)
-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
-- open import Data.Sum.Base using (_⊎_)
-- open import Function.Base  using (_∘_)
-- open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝)
-- open import Agda.Builtin.Bool using (true; false)
-- open import Relation.Nullary using (Dec; _because_; ofʸ)


-- open import Data.Product using (∃; ∃-syntax)


-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- A binary variant of _Preserves_⟶_.
_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)



--------------------------------------------------------------------- -->
