---
layout: title-page
title : the cubical-algebras library
date : 2021-05-08
author: William DeMeo
---

My ~/.agda/libraries file looks like this:

```
~/opt/AGDA/agda-stdlib-1.6/standard-library.agda-lib
~/git/hub/ualib/TypeTopology/typetopology.agda-lib
~/git/hub/ualib/cubical/cubical.agda-lib
```

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

module CubicalStructures where

open import overture
open import relations
open import algebras
open import homs

\end{code}

--------------------------

{% include UALib.Links.md %}

