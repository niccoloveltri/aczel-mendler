{-# OPTIONS --cubical #-}

module Main where

-- ==============================================
-- A FINAL COALGEBRA THEOREM IN HOTT 
-- ==============================================

-- Some preliminaries
open import Utilities

-- Coalgebras
open import Coalgebras

-- Construction of the weakly-complete coalgebra
open import WeaklyComplete

-- Precongruences and quotienting by the largest precongruence
open import Precongruences
open import MaxQuotExt

-- Construction of the complete coalgebra, assuming propositional
-- resizing.
open import Complete

-- The multiset functor, Gylterud-style
open import Multiset

-- Set-based functors
open import SetBased

-- From completeness to finality.
-- In particular, every set-based functor admits a final coalgebra,
-- assuming propositional resizing.
open import Final

-- The powerset functor and its final coalgebra
open import Powerset
