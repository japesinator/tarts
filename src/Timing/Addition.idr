module Timing.Addition

import Data.Fin
import Data.Vect
import Timing.Equality

-- Left and right byte shifts

lShift : Byte ->
         Byte
lShift v = tail v ++ [Zero]

rShift : Byte ->
         Byte
rShift = (::) Zero . take 7

-- A full adder

fullAdder : Bit ->     -- The first input bit
            Bit ->     -- The second input bit
            Bit ->     -- The input carry
            (Bit, Bit) -- The sum and then the output carry
fullAdder a b ci = (s, co) where
  s  = bitXor a $ bitXor b ci
  co = bitOr (bitAnd a b) $ bitOr (bitAnd a ci) (bitAnd b ci)

-- Unify a tuple of two counting variables into a tuple of a tuple and a count

unifyCount : ((a, Nat), (a, Nat)) ->
             ((a, a), Nat)
unifyCount t = (((fst $ fst t), (fst $ snd t)), (snd $ fst t) + (snd $ snd t))

-- A counting full adder

countingFullAdder : Bit ->
                    Bit ->
                    Bit ->
                    ((Bit, Bit), Nat)
countingFullAdder a b ci = unifyCount (s, co) where
  a' : (Bit, Nat)
  a'  = (a,  Z)
  b'  : (Bit, Nat)
  b'  = (b,  Z)
  ci' : (Bit, Nat)
  ci' = (ci, Z)
  bitAnd' : (Bit, Nat) -> (Bit, Nat) -> (Bit, Nat)
  bitAnd' = addCount bitAnd
  bitOr' : (Bit, Nat) -> (Bit, Nat) -> (Bit, Nat)
  bitOr'  = addCount bitOr
  bitXor' : (Bit, Nat) -> (Bit, Nat) -> (Bit, Nat)
  bitXor' = addCount bitXor
  s  = bitXor' a' $ bitXor' b' ci'
  co = bitOr' (bitAnd' a' b') $ bitOr' (bitAnd' a' ci') (bitAnd' b' ci')

-- A proof that the counting full adder runs in constant time
numericTimeConstancyOfAdder : (a, b, c : Bit) ->
                              snd $ countingFullAdder a b c = 7
numericTimeConstancyOfAdder _ _ _ = Refl

timeConstancyOfAdder : (a, b, c, d, e, f : Bit) ->
                       snd $ countingFullAdder a b c
                     = snd $ countingFullAdder d e f
timeConstancyOfAdder _ _ _ _ _ _ = Refl

instance Num (Fin n) where
  (+)         = assert_total (+)
  (-)         = with Fin     (-)
  (*)         = assert_total (*)
  abs         =              id
  fromInteger = assert_total fromInteger

addBytes : Byte ->
           Byte ->
           Byte
addBytes a b = map fst $ zipWith3 fullAdder a b
             $ map (carry . fromInteger) $ fromList $ enumFromTo 0 7 where
  carry : Fin 8 -> Bit
  carry FZ     = Zero
  carry (FS k) = snd $ fullAdder (index (FS k) a)
                                 (index (FS k) b) $ carry $ weaken k
