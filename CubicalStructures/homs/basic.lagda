---
layout: default
title : homs.basic
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ) -- ; _×_)
open import Cubical.Data.Sigma.Base using (_×_)
open import Function.Base  using (_∘_; id)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)
-- open import Cubical.Foundations.Prelude using (funExt; i0; i1; _≡_; refl)

-- Imports from the Agda Universal Algebra Library
open import structures.basic
open import overture.preliminaries using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; ∣_∣; ∥_∥; fst; _∙_; snd)
open import overture.inverses using (IsInjective; IsSurjective)
open import relations.discrete using (ker; ker') -- 𝟎; _|:_)

module homs.basic {𝑅 : Signature}{𝐹 : Signature} where


module _ {α β : Level} (𝑨 : Structure α 𝑅 𝐹)(𝑩 : Structure β 𝑅 𝐹) where

 comp-rel : ∣ 𝑅 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (ℓ₁ ⊔ α)
 comp-rel R h = ∀ a → ((R ʳ 𝑨) a) ≡ (R ʳ 𝑩) (h ∘ a)

 is-hom-rel : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (ℓ₁ ⊔ α)
 is-hom-rel h = ∀ R →  comp-rel R h

 comp-op : ∣ 𝐹 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 comp-op f h = ∀ a → h ((f ᵒ 𝑨) a) ≡ (f ᵒ 𝑩) (h ∘ a)

 is-hom-op : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (α ⊔ β)
 is-hom-op h = ∀ f → comp-op f h

 is-hom : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (ℓ₁ ⊔ α ⊔ β)
 is-hom h = is-hom-rel h × is-hom-op h

 hom : Type (ℓ₁ ⊔ α ⊔ β)
 hom = Σ[ h ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-hom h

module _ {α β γ : Level} (𝑨 : Structure α 𝑅 𝐹){𝑩 : Structure β 𝑅 𝐹}(𝑪 : Structure γ 𝑅 𝐹) where

 ∘-is-hom-rel : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →             is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel {f}{g} fhr ghr R a = fhr R a ∙ ghr R (f ∘ a)

 ∘-is-hom-op : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →            is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op {f}{g} fho gho 𝑓 a = cong g (fho 𝑓 a) ∙ gho 𝑓 (f ∘ a)

 ∘-is-hom : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →         is-hom 𝑨 𝑩 f → is-hom 𝑩 𝑪 g → is-hom 𝑨 𝑪 (g ∘ f)
 ∘-is-hom {f} {g} fhro ghro = ihr , iho
  where
  ihr : is-hom-rel 𝑨 𝑪 (g ∘ f)
  ihr = ∘-is-hom-rel {f}{g} ∣ fhro ∣ ∣ ghro ∣

  iho : is-hom-op 𝑨 𝑪 (g ∘ f)
  iho = ∘-is-hom-op {f}{g} ∥ fhro ∥ ∥ ghro ∥

 ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
 ∘-hom (f , fh) (g , gh) = g ∘ f , ∘-is-hom {f}{g} fh gh


𝒾𝒹 : {α : Level}(𝑨 : Structure α 𝑅 𝐹) → hom 𝑨 𝑨
𝒾𝒹 _ = id , (λ R a → refl) , (λ f a → refl)

module _ {α β : Level} where

 is-mon : (𝑨 : Structure α 𝑅 𝐹)(𝑩 : Structure β 𝑅 𝐹) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (ℓ₁ ⊔ α ⊔ β)
 is-mon 𝑨 𝑩 g = is-hom 𝑨 𝑩 g × IsInjective g

 mon : Structure α 𝑅 𝐹 → Structure β 𝑅 𝐹  → Type (ℓ₁ ⊔ α ⊔ β)
 mon 𝑨 𝑩 = Σ[ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-mon 𝑨 𝑩 g

 is-epi : (𝑨 : Structure α 𝑅 𝐹)(𝑩 : Structure β 𝑅 𝐹) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type (ℓ₁ ⊔ α ⊔ β)
 is-epi 𝑨 𝑩 g = is-hom 𝑨 𝑩 g × IsSurjective g

 epi : Structure α 𝑅 𝐹 → Structure β 𝑅 𝐹  → Type (ℓ₁ ⊔ α ⊔ β)
 epi 𝑨 𝑩 = Σ[ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epi 𝑨 𝑩 g

 mon-to-hom : (𝑨 : Structure α 𝑅 𝐹){𝑩 : Structure β 𝑅 𝐹} → mon 𝑨 𝑩 → hom 𝑨 𝑩
 mon-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

 epi-to-hom :  {𝑨 : Structure α 𝑅 𝐹}(𝑩 : Structure β 𝑅 𝐹) → epi 𝑨 𝑩 → hom 𝑨 𝑩
 epi-to-hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

\end{code}


-- open Lift

-- 𝓁𝒾𝒻𝓉 : {α β : Level}{𝑨 : Structure α 𝑅 𝐹} → hom 𝑨 (Lift-str 𝑨 β)
-- 𝓁𝒾𝒻𝓉 = lift , 𝒾𝒹

-- 𝓁ℴ𝓌ℯ𝓇 : {α β : Level}{𝑨 : Structure α 𝑅 𝐹} → hom (Lift-str 𝑨 β) 𝑨
-- 𝓁ℴ𝓌ℯ𝓇 = lower , 𝒾𝒹

#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation θ, there exists a homomorphism with kernel θ (namely, that canonical projection onto the quotient modulo θ).

\begin{code}

module _ {α β : Level}{𝑨 : Structure α 𝑅 𝐹} where
 homker-comp : funext ℓ₀ β → {𝑩 : Structure β 𝑅 𝐹}(h : hom 𝑨 𝑩) → compatible 𝑨 (ker ∣ h ∣)
 homker-comp fe {𝑩} h f {u}{v} kuv = ∣ h ∣((f ᵒ 𝑨) u)   ≡⟨ ∥ snd h ∥ f u ⟩
                                  (f ᵒ 𝑩)(∣ h ∣ ∘ u) ≡⟨ cong (f ᵒ 𝑩) goal ⟩
                                  (f ᵒ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ snd h ∥ f v)⁻¹ ⟩
                                  ∣ h ∣((f ᵒ 𝑨) v)   ∎
  where
  goal : (λ x → ∣ h ∣ (u x)) ≡ (λ x → ∣ h ∣ (v x))
  goal = fe (λ x → kuv x)
  -- k : ∀ x → ∣ h ∣ (u x) ≡ ∣ h ∣ (v x)
  -- k = kuv
  -- k' : ({x : A} → PathP (B x) (f {x}) (g {x}))
  -- goal : (λ x → ∣ h ∣ (u x)) ≡ (λ x → ∣ h ∣ (v x))
  -- goal = funExt {f = (λ x → (∣ h ∣ (u x) i0))}{g = (λ x → ∣ h ∣ (v x) i1)} kuv

-- Next: try to use the following (cubical) funExt *theorem* instead of funext axiom.
-- funExt : {B : A → I → Type ℓ'}
--   {f : (x : A) → B x i0} {g : (x : A) → B x i1}
--   → ((x : A) → PathP (B x) (f x) (g x))
--   → PathP (λ i → (x : A) → B x i) f g
-- funExt p i x = p x i


\end{code}















---------- The rest is not yet integrated ------------------------------------------------









(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.


 kercon : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Con{𝓤}{𝓦} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.


 kerquo : swelldef 𝓥 𝓦 → {𝑩 : Algebra 𝓦 𝑆} → hom 𝑨 𝑩 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)


ker[_⇒_]_↾_ : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆) → hom 𝑨 𝑩 → swelldef 𝓥 𝓦 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

\end{code}

Thus, given `h : hom 𝑨 𝑩`, we can construct the quotient of `𝑨` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `𝑨 [ 𝑩 ]/ker h ↾ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.


module _ {𝓤 𝓦 : Level}{𝑨 : Algebra 𝓤 𝑆} where
 πepi : (θ : Con{𝓤}{𝓦} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  cπ-is-epic (C , (a , refl)) =  Image_∋_.im a

\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.


 πhom : (θ : Con{𝓤}{𝓦} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)


 πker : (wd : swelldef 𝓥 𝓦){𝑩 : Algebra 𝓦 𝑆}(h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)
 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef 𝓥 (𝓤 ⊔ lsuc 𝓦)}(θ : Con 𝑨)
  →           ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra 𝓦 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.


module _ {𝓘 𝓦 : Level}{I : Type 𝓘}(ℬ : I → Algebra 𝓦 𝑆) where

 ⨅-hom-co : funext 𝓘 𝓦 → {𝓤 : Level}(𝑨 : Algebra 𝓤 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra 𝓤 𝑆 and ℬ : I → Algebra 𝓦 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.


 ⨅-hom : funext 𝓘 𝓦 → {𝓤 : Level}(𝒜 : I → Algebra 𝓤 𝑆) → Π[ i ꞉ I ] hom (𝒜 i)(ℬ i) → hom (⨅ 𝒜)(⨅ ℬ)
 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 ⨅-projection-hom : Π[ i ꞉ I ] hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.


{% include UALib.Links.md %}









Detailed proofs.
```
 ∘-is-hom-rel : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →             is-hom-rel 𝑨 𝑩 f → is-hom-rel 𝑩 𝑪 g → is-hom-rel 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-rel {f}{g} fhr ghr R a = pf
  where
  pf : ((R ʳ 𝑨) a) ≡ (R ʳ 𝑪)(g ∘ f ∘ a)
  pf = (R ʳ 𝑨) a          ≡⟨ fhr R a ⟩
       (R ʳ 𝑩)(f ∘ a)     ≡⟨ ghr R (f ∘ a)⟩
       (R ʳ 𝑪)(g ∘ f ∘ a) ∎

 ∘-is-hom-op : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →            is-hom-op 𝑨 𝑩 f → is-hom-op 𝑩 𝑪 g → is-hom-op 𝑨 𝑪 (g ∘ f)
 ∘-is-hom-op {f}{g} fho gho 𝑓 a = pf
  where
  pf : (g ∘ f) ((𝑓 ᵒ 𝑨) a) ≡ (𝑓 ᵒ 𝑪) (λ x → (g ∘ f) (a x))
  pf = (g ∘ f) ((𝑓 ᵒ 𝑨) a) ≡⟨ cong g (fho 𝑓 a)⟩
       g ((𝑓 ᵒ 𝑩)(f ∘ a)) ≡⟨ gho 𝑓 (f ∘ a) ⟩
       (𝑓 ᵒ 𝑪) (λ x → (g ∘ f) (a x)) ∎


```
  hghr : ∀ R a → ((R ʳ 𝑨) a) ≡ (R ʳ 𝑪)(h ∘ g ∘ a)
  hghr R a = (R ʳ 𝑨) a          ≡⟨ ghr R a ⟩
             (R ʳ 𝑩)(g ∘ a)     ≡⟨ hhr R (g ∘ a)⟩
             (R ʳ 𝑪)(h ∘ g ∘ a) ∎

  hgho : ∀ 𝑓 a → (h ∘ g)((𝑓 ᵒ 𝑨) a) ≡ (𝑓 ᵒ 𝑪)(h ∘ g ∘ a)
  hgho 𝑓 a = (h ∘ g)((𝑓 ᵒ 𝑨) a) ≡⟨ cong h (gho 𝑓 a)⟩
             h ((𝑓 ᵒ 𝑩)(g ∘ a)) ≡⟨ hho 𝑓 (g ∘ a)⟩
             (𝑓 ᵒ 𝑪)(h ∘ g ∘ a) ∎
