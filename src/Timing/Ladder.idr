module Timing.Ladder
-- http://cr.yp.to/bib/2003/joye-ladder.pdf

import Count

bitAtIndex : Nat -> -- Index to check
             Nat -> -- Number to check
             Nat    -- Z or (S Z)
bitAtIndex i n = case (>=) (mod n (pow 2 (S i))) (pow 2 i) of
                      True  => (S Z)
                      False => Z

mapFst : (a -> b) ->
         (a, c) ->
         (b, c)
mapFst f (a, b) = (f a, b)

mapSnd : (a -> b) ->
         (c, a) ->
         (c, b)
mapSnd f (a, b) = (a, f b)

ladderStep : Nat ->        -- Index
             Nat ->        -- Exponent
             (Nat, Nat) -> -- Intermediate variables (r0, r1)
             (Nat, Nat)    -- New intermediate variables
ladderStep i e = case bitAtIndex i e of
                      Z     => (the ((Nat, Nat) -> (Nat, Nat))
                                    (\(x, y) => (x * x, y))) .
                               (the ((Nat, Nat) -> (Nat, Nat))
                                    (\(x, y) => (x, x * y)))
                      (S Z) => (the ((Nat, Nat) -> (Nat, Nat))
                                    (\(x, y) => (y * x, y))) .
                               (the ((Nat, Nat) -> (Nat, Nat))
                                    (\(x, y) => (x, y * y)))
-- FIXME: idris likes to know the types of lambda expressions, but that makes ugly code

countingLStep : Nat ->              -- We shouldn't need a count on the index
                Nat ->              -- Ditto for the exponent
                Count (Nat, Nat) -> -- We just store the opcount in the intermediate
                                    --   variables
                Count (Nat, Nat)    -- We carry the count forward
countingLStep i e = case bitAtIndex i e of
                         Z     => mapFst (the ((Nat, Nat) -> (Nat, Nat))
                                        (\(x, y) => (x * x, y))) .
                                  mapFst (the ((Nat, Nat) -> (Nat, Nat))
                                        (\(x, y) => (x, x * y))) .
                                  mapSnd ((+) 3) -- `map` is weird here, so
                                                 --   we use 3 (`*` + `*` +
                                                 --   `case`)
                         (S Z) => mapFst (the ((Nat, Nat) -> (Nat, Nat))
                                        (\(x, y) => (y * x, y))) .
                                  mapFst (the ((Nat, Nat) -> (Nat, Nat))
                                        (\(x, y) => (x, y * y))) .
                                  mapSnd ((+) 3)
