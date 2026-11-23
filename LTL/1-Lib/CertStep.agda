{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.CertStep -- the kinds of step in a certificate of
-- LTL.1-Lib.FairGraph, one per constructor of Cert; certShape lists them in
-- removal order.
--
-- A module of its own because FairGraph is parameterised by its graph: a type
-- declared there would take the graph too, and the shapes of two graphs would
-- have different types.

module LTL.1-Lib.CertStep where

data CertStep : Set where
  removedSink removedBlock emptied : CertStep
