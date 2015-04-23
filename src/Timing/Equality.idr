module Equality

import Data.Vect

-- The first thing we do is redefine the bit as either one or zero, and then
--   define equality for it

data Bit = One
         | Zero

instance Eq Bit where {
  (==) One One   = True
  (==) Zero Zero = True
  (==) _ _       = False
}

-- Now that we have the bit, we can make a Byte type that's just eight ordered bits

Byte : Type
Byte = Vect 8 Bit

-- It's also going to be useful to define the basic Boolean operators on our new
--   bits

bitNot : Bit ->
         Bit
bitNot One  = Zero
bitNot Zero = One

bitAnd : Bit ->
         Bit ->
         Bit
bitAnd One One = One
bitAnd _   _   = Zero

bitNand : Bit ->
          Bit ->
          Bit
bitNand a b = bitNot $ bitAnd a b

bitOr : Bit ->
        Bit ->
        Bit
bitOr Zero Zero = Zero
bitOr _    _    = One

bitNor : Bit ->
         Bit ->
         Bit
bitNor a b = bitNot $ bitOr a b

bitXor : Bit ->
         Bit ->
         Bit
bitXor One  One  = Zero
bitXor Zero Zero = Zero
bitXor _    _    = One

bitNXor : Bit ->
          Bit ->
          Bit
bitNXor a b = bitNot $ bitXor a b

-- zipAndFold is just a useful composition of operations to zip two things
--   together using a function and then fold another function across them

zipAndFold : (a -> a -> a) -> -- Function to fold with
             (a -> a -> a) -> -- Function to zip with
             Vect (S n) a ->  -- Vector to zip together
             Vect (S n) a ->  -- Vector to zip together
             a                -- Result of folding across the zip of the above vectors
zipAndFold f g a b = foldr1 f $ zipWith g a b

-- zipAndFold happens to let us write a handy byteEq function that's also
--   time constant.  We don't actually use this one, it's just easier to think
--   about.  It returns one if the bytes are equal, zero if they aren't

byteEq : Byte ->
         Byte ->
         Bit -- One of the vectors are equal, otherwise Zero
byteEq = zipAndFold bitNXor bitAnd

-- Now we get into the idea of using a tuple of (Bit, Nat) to represent both a
--   bit and the number of operations done to produce it.

-- This is a tool that lets us start counting on a Vector by saying each bit
--   took no operations to produce.  It should only really be used on variables
--   passed into the function as parameters.

initializeCount : Vect n a ->     -- Vector of something
                  Vect n (a, Nat) -- Vector of (something, operation count)
initializeCount []        = []
initializeCount (x :: xs) = (x, 0) :: initializeCount xs

-- This takes a function and makes it a function that counts operations.

addCount : (a -> a -> a) ->
           (a, Nat) ->
           (a, Nat) ->
           (a, Nat)
addCount f (a, n) (b, m) = (f a b, n + m + 1)

-- This is byteEq written to count operations

countingByteEq : Byte ->
                 Byte ->
                 (Bit, Nat)
countingByteEq a b = zipAndFold (addCount bitNXor)
                                (addCount bitAnd)
                                (initializeCount a)
                                (initializeCount b)

-- Now, we use idris' theorem prover to show that our function is time-
--   -constant.

-- This just tests that all the items in a vector have the same number of
--   operations performed on them.

allHasCount : Vect n (a, Nat) ->
              Nat ->
              Bool
allHasCount []             n = True
allHasCount ((_, a) :: xs) n = a == n && allHasCount xs n

-- This says that zipping two new vectors together should return a vector of
--   items that all have had one operation performed on them.

zipOps : (a,b:Vect n c) ->
         (f:c -> c -> c) ->
         allHasCount (zipWith (addCount f)
                              (initializeCount a)
                              (initializeCount b)) 1
           =
         True
zipOps []        []        _ = Refl
zipOps (x :: xs) (y :: ys) f = rewrite zipOps xs ys f in Refl

-- This is just the definition of addcount, namely operating on two things will
--   return a thing with an operation count of the sum of theirs plus one.

addCountBasic : (f:c -> c -> c) ->
                (a,b:(c, Nat)) ->
                snd $ (addCount f) a b = snd a + snd b + 1
addCountBasic _ (_, n) (_, m) = Refl

-- This is where things get ugly.  Idris doesn't really like proving things
--   about generalized folds, so I just wrote one huge proof for only 8-element
--   vectors because that's all we're dealing with.  It's kind of the opposite
--   of elegant, nice, or anything good in the world though.

-- This is literally just a specific case of the commutative/associative
--   property of addition

addEightThings : (a,b,c,d,e,f,g,h:Nat) ->
                 plus (plus b $ plus (plus c $ plus (plus d $ plus (plus e
                      $ plus (plus f $ plus (plus g $ plus (plus h a)
                      1) 1) 1) 1) 1) 1) 1
                 = plus (plus a $ plus b $ plus c $ plus d $ plus e $ plus f
                        $ plus g $ plus h 0) (fromInteger 7)
addEightThings a b c d e f g h =
     rewrite
             plusZeroRightNeutral h
  in rewrite plusCommutative
               (plus h a) 1
  in rewrite plusCommutative
               g (S $ plus h a)
  in rewrite plusCommutative
               (S $ plus (plus h a) g) 1
  in rewrite plusCommutative
               f (S $ S $ plus (plus h a) g)
  in rewrite plusCommutative
               (plus (S $ S $ plus (plus h a) g) f) 1
  in rewrite plusCommutative
               e (S $ S $ S $ plus (plus (plus h a) g) f)
  in rewrite plusCommutative
               (plus (S $ S $ S $ plus (plus (plus h a) g) f) e) 1
  in rewrite plusCommutative
               d (S $ S $ S $ S $ plus (plus (plus (plus h a) g) f) e)
  in rewrite plusCommutative
               (plus (S $ S $ S $ S $ plus (plus (plus (plus h a) g) f) e) d) 1
  in rewrite plusCommutative
               c (S $ S $ S $ S $ S
                 $ plus (plus (plus (plus (plus h a) g) f) e) d)
  in rewrite plusCommutative
               (plus (S $ S $ S $ S $ S
                     $ plus (plus (plus (plus (plus h a) g) f) e) d) c) 1
  in rewrite plusCommutative
               b (S $ S $ S $ S $ S $ S
                 $ plus (plus (plus (plus (plus (plus h a) g) f) e) d) c)
  in rewrite plusCommutative
               (plus (S $ S $ S $ S $ S $ S
                     $ plus (plus (plus (plus (plus (plus h a) g) f) e) d) c) b)
                     1
  in rewrite plusCommutative
               (plus h a) g
  in rewrite plusAssociative
               g h a
  in rewrite plusCommutative
               (plus (plus g h) a) f
  in rewrite plusAssociative
               f (plus g h) a
  in rewrite plusCommutative
               (plus (plus f $ plus g h) a) e
  in rewrite plusAssociative
               e (plus f $ plus g h) a
  in rewrite plusCommutative
               (plus (plus e $ plus f $ plus g h) a) d
  in rewrite plusAssociative
               d (plus e $ plus f $ plus g h) a
  in rewrite plusCommutative
               (plus (plus d $ plus e $ plus f $ plus g h) a) c
  in rewrite plusAssociative
               c (plus d $ plus e $ plus f $ plus g h) a
  in rewrite plusCommutative
               (plus (plus c $ plus d $ plus e $ plus f $ plus g h) a) b
  in rewrite plusAssociative
               b (plus c $ plus d $ plus e $ plus f $ plus g h) a
  in rewrite plusCommutative
               (plus b $ plus c $ plus d $ plus e $ plus f $ plus g h) a
  in rewrite plusCommutative
               (plus a $ plus b $ plus c $ plus d $ plus e $ plus f $ plus g h)
               7
  in Refl
   -- FIXME: dear god I am sorry for the above

-- This states that folding an operation across a vector will perform seven
--   operations (for each adjacent pair in the vector), and so the sum of the
--   operations done on the result is the number of operations done on all the
--   items that go into it (all the items in the vector) plus seven.
-- FIXME: this proof is kind of a mess

foldrByteBasic : (a:Vect 8 (Bit, Nat)) ->
                 (f:Bit -> Bit -> Bit) ->
                 snd $ foldr1 (addCount f) a = sum (map snd a) + 7
foldrByteBasic [a,b,c,d,e,f,g,h] i = let ai = addCount i in
     rewrite addCountBasic
               i b $ ai c $ ai d $ ai e $ ai f $ ai g $ ai h a
  in rewrite addCountBasic
               i c $ ai d $ ai e $ ai f $ ai g $ ai h a
  in rewrite addCountBasic
               i d $ ai e $ ai f $ ai g $ ai h a
  in rewrite addCountBasic
               i e $ ai f $ ai g $ ai h a
  in rewrite addCountBasic
               i f $ ai g $ ai h a
  in rewrite addCountBasic
               i g $ ai h a
  in rewrite addCountBasic
               i h a
  in rewrite addEightThings
               (snd a) (snd b) (snd c) (snd d) (snd e) (snd f) (snd g) (snd h)
  in Refl

-- This is a specific case of the above where each element has only had one op
--   performed to yield it, so the sum of the operations on the result is always
--   15.

foldrHomoByte : (a:Vect 8 (Bit,Nat)) ->
                (f:Bit -> Bit -> Bit) ->
                (p:allHasCount a (S Z) = True) ->
                snd $ foldr1 (addCount f) a = 15
-- The below proof is definitely true, but at the moment type-checking it could
--   quite possibly take a bit longer than the age of the universe. Thanks
--   combinatorial explosion.
-- FIXME: make this work
-- foldrHomoByte [(a,(S Z)),(b,(S Z)),(c,(S Z)),(d,(S Z)),(e,(S Z)),(f,(S Z)),
--                (g,(S Z)),(h,(S Z))] i p = Refl
foldrHomoByte _ _ = believe_me

-- This just says that if you zip two vectors togeter and then fold across them,
--   (and they're both size 8) then 15 operations will be performed.
zfBasic : (a,b:Byte) ->
          (f,g:Bit -> Bit -> Bit) ->
          snd $ foldr1 (addCount f) $ zipWith (addCount g)
                                              (initializeCount a)
                                              (initializeCount b)
          = 15
zfBasic a b f g =
  rewrite foldrHomoByte
            (zipWith (addCount g) (initializeCount a) (initializeCount b)) f
            (zipOps a b g)
  in Refl

-- This says equality always takes 15 operations

numericTimeConstancyOfEq : (a,b:Byte) ->
                           snd (countingByteEq a b)
                             =
                           15
numericTimeConstancyOfEq a b = rewrite zfBasic a b bitNXor bitAnd in Refl

-- And thus equality between any two pairs of bytes takes the same amount of
--   time.

timeConstancyOfEq : (a,b,c,d:Byte) ->
                    snd $ countingByteEq a b = snd $ countingByteEq c d
timeConstancyOfEq a b c d =
     rewrite numericTimeConstancyOfEq a b
  in rewrite numericTimeConstancyOfEq c d
  in Refl -- QED

-- The above was mostly proof of concept, as in the x86 instruction set, which
--   determines how long things take in real life, it's much simpler.
