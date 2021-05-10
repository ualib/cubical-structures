---
layout: default
title : relations.discrete module
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base  using (_∘_)
open import Relation.Binary.Core using (REL; Rel; _⇒_;_=[_]⇒_)
open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝)

open import overture.preliminaries using (Type; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; -Σ)

module relations.discrete where


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
 𝟎-sigma = Σ[ x ꞉ A ] Σ[ y ꞉ A ] x ≡ y

 𝟎-sigma' : Type 𝓤
 𝟎-sigma' = Σ[ (x , y) ꞉ A × A ] x ≡ y

--The type of operations
Op : Type 𝓥 → Type 𝓤 → Type(𝓤 ⊔ 𝓥)
Op I A = (I → A) → A

π : {I : Type 𝓥 } {A : Type 𝓤 } → I → Op I A
π i x = x i

eval-rel : {A : Type 𝓤}{I : Type 𝓥} → Rel A 𝓦 → Rel (I → A)(𝓥 ⊔ 𝓦)
eval-rel R u v = ∀ i → R (u i) (v i)

_|:_ : {A : Type 𝓤}{I : Type 𝓥} → Op I A → Rel A 𝓦 → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
f |: R  = (eval-rel R) =[ f ]⇒ R

compatible-op : {A : Type 𝓤}{I : Type 𝓥} → (f : Op I A)(R : Rel A 𝓦) → Type(𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

\end{code}



--------------------------------------


{% include cubical-algebras.links.md %}
