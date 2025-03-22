{-# OPTIONS --cubical #-}

module Main where

-- ==============================================
-- A TERMINAL COALGEBRA THEOREM IN HOTT 
-- ==============================================

-- Some preliminaries
open import Utilities

-- Coalgebras
open import Coalgebras

-- Construction of the weakly U-terminal coalgebra
open import WeaklyUTerminal

-- Precongruences and quotienting by the largest precongruence
open import Precongruences
open import MaxQuotExt

-- Construction of the U-terminal coalgebra, assuming propositional
-- resizing.
open import UTerminal

-- The multiset functor P∞, Gylterud-style
open import Multiset

-- U-based functors
open import UBased

-- From U-terminal to terminal.
-- In particular, every U-based functor admits a final coalgebra,
-- assuming propositional resizing.
open import Terminal

