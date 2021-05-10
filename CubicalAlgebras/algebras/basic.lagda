---
layout: default
title : algebras.basic module (of the cubical-algebras library)
date : 2021-05-08
author: William DeMeo
---

### <a id="algebras">Basic Definitions</a>

This section presents the [algebras.basic][] module of the [cubical-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Data.Empty using (⊥)
open import Agda.Builtin.Bool
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Product renaming (_,_ to infixr 50 _,_) using (Σ; _×_)
open import Relation.Binary using (Rel)

-- Imports from the Agda Universal Algebra Library
open import overture.preliminaries using (Type; 𝓞; 𝓤; 𝓥; 𝓦; -Σ; ∣_∣; ∥_∥)
open import relations.continuous using (ContRel; DepRel; cont-compatible-op; dep-compatible-op)
open import relations.discrete using (Op; _|:_)

module algebras.basic where

Signature : (𝓞 𝓥 : Level) → Type (lsuc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ꞉ Type 𝓞 ] (F → Type 𝓥)

data monoid-op {𝓞 : Level} : Type 𝓞 where
 e : monoid-op; · : monoid-op

monoid-sig : Signature 𝓞 lzero
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }


Algebra : (𝓤 : Level)(𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc 𝓤)
Algebra 𝓤 𝑆 = Σ[ A ꞉ Type 𝓤 ]                   -- the domain
              ∀ (f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A    -- the basic operations


level-of-alg : {𝑆 : Signature 𝓞 𝓥} → Algebra 𝓤 𝑆 → Level
level-of-alg {𝓤 = 𝓤} _ = 𝓤


record algebra (𝓤 : Level) (𝑆 : Signature 𝓞 𝓥) : Type(lsuc(𝓞 ⊔ 𝓥 ⊔ 𝓤)) where
 constructor mkalg
 field
  univ : Type 𝓤
  op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ


module _ {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥


 _̂_ : (𝑓 : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 𝑓 ̂ 𝑨 = λ 𝑎 → (∥ 𝑨 ∥ 𝑓) 𝑎


open Lift

Lift-op : {𝓘 : Level}{I : Type 𝓘}{A : Type 𝓤} → Op I A → (𝓦 : Level) → Op I (Lift 𝓦 A)
Lift-op f 𝓦 = λ x → lift (f (λ i → lower (x i)))

Lift-alg : {𝑆 : Signature 𝓞 𝓥} → Algebra 𝓤 𝑆 → (𝓦 : Level) → Algebra (𝓤 ⊔ 𝓦) 𝑆
Lift-alg {𝑆 = 𝑆} 𝑨 𝓦 = Lift 𝓦 ∣ 𝑨 ∣ , (λ (𝑓 : ∣ 𝑆 ∣) → Lift-op (𝑓 ̂ 𝑨) 𝓦)

open algebra

Lift-alg-record-type : {𝑆 : Signature 𝓞 𝓥} → algebra 𝓤 𝑆 → (𝓦 : Level) → algebra (𝓤 ⊔ 𝓦) 𝑆
Lift-alg-record-type {𝑆 = 𝑆} 𝑨 𝓦 = mkalg (Lift 𝓦 (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → Lift-op ((op 𝑨) f) 𝓦)


compatible : {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
compatible  𝑨 R = ∀ 𝑓 → (𝑓 ̂ 𝑨) |: R


module _ {I : Type 𝓥} {𝑆 : Signature 𝓞 𝓥} where

 cont-compatible : (𝑨 : Algebra 𝓤 𝑆) → ContRel I ∣ 𝑨 ∣ 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
 cont-compatible 𝑨 R = ∀ (𝑓 : ∣ 𝑆 ∣ ) →  cont-compatible-op (𝑓 ̂ 𝑨) R

 dep-compatible : (𝒜 : I → Algebra 𝓤 𝑆) → DepRel I (λ i → ∣ 𝒜  i ∣) 𝓦 → Type(𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦)
 dep-compatible 𝒜 R = ∀ ( 𝑓 : ∣ 𝑆 ∣ ) →  dep-compatible-op (λ i → 𝑓 ̂ (𝒜 i)) R

\end{code}



--------------------------------------

{% include UALib.Links.md %}

















