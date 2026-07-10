{-# OPTIONS --prop --postfix-projections --safe #-}

-- Integration point for the paper's mechanised claims.
module everything where

-- The examples of Section 5, one interpretation instance per semiring. Each instance pulls in
-- the interpretation of the higher-order language (Section 4) over the self-dual semimodule
-- models (Section 3), and with them the supporting theory: the category of families and its
-- exponentials, and the definability results of Section 6 in the conservativity module.
import example.all

-- Section 6 "Correctness of the Higher-Order Interpretation": the Fiore and Simpson 1999
-- definability theorem and its consequences. Also reached via ho-model; imported directly so the
-- gate does not depend on that.
import conservativity
