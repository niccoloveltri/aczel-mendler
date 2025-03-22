{-# OPTIONS --cubical #-}

module Main where

-- ==============================================
-- A DIFFERENT TERMINAL COALGEBRA THEOREM IN HOTT 
-- ==============================================

-- Some preliminaries
open import Utilities

-- Coalgebras
open import Coalgebras

-- Construction of the weakly-SetU-terminal coalgebra
open import WeaklySetUTerminal

-- Precongruences and quotienting by the largest precongruence
open import Precongruences
open import MaxQuotExt

-- Construction of the SetU-terminal coalgebra, assuming propositional
-- resizing.
open import SetUTerminal

-- The multiset functor P∞, Gylterud-style
open import Multiset

-- SetU-based functors
open import SetUBased

-- From SetU-terminal to Set-terminal
-- In particular, every SetU-based functor admits a Set-terminal coalgebra,
-- assuming propositional resizing.
open import SetTerminal

-- The powerset functor and its terminal coalgebra
open import Powerset
