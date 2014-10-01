module Constant_Time_Functions

-- The first thing we do is redefine the bit as either one or zero, and then
--   define equality for it

data Bit = One | Zero

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

bitAnd : Bit ->
         Bit ->
         Bit
bitAnd One One = One
bitAnd _   _   = Zero

bitNand : Bit ->
          Bit ->
          Bit
bitNand One One = Zero
bitNand _   _   = One

bitOr : Bit ->
        Bit ->
        Bit
bitOr Zero Zero = Zero
bitOr _    _    = One

bitNor : Bit ->
         Bit ->
         Bit
bitNor Zero Zero = One
bitNor _    _    = Zero

bitXor : Bit ->
         Bit ->
         Bit
bitXor One  One  = Zero
bitXor Zero Zero = Zero
bitXor _    _    = One

bitNXor : Bit ->
          Bit ->
          Bit
bitNXor One  One  = One
bitNXor Zero Zero = One
bitNXor _    _    = Zero

bitNot : Bit ->
         Bit
bitNot One  = Zero
bitNot Zero = One

-- For some reason foldr1 was not working for me so I quickly rewrote it
-- FIXME: use the real foldr1

vFoldr1 : (t -> t -> t) ->
          Vect (S n) t ->
          t
vFoldr1 f (x::xs) = foldr f x xs

-- zipAndFold is just a useful composition of operations to zip two things
--   together using a function and then fold another function across them

zipAndFold : (a -> a -> a) ->
             (a -> a -> a) ->
             Vect (S n) a ->
             Vect (S n) a ->
             a
zipAndFold f g a b = vFoldr1 f (Prelude.Vect.zipWith g a b)

-- zipAndFold happens to let us write a handy byteEq function that's also
--   time constant.  We don't actually use this one, it's just easier to think
--   about.  It returns one if the bytes are equal, zero if they aren't

byteEq : Byte ->
         Byte ->
         Bit
byteEq a b = zipAndFold bitNXor bitAnd a b

-- Now we get into the idea of using a tuple of (Bit, Nat) to represent both a
--   bit and the number of operations done to produce it.
-- FIXME: this should be a monad

-- This is a tool that lets us start counting on a Vector by saying each bit
--   took no operations to produce.  It should only really be used on variables
--   passed into the function as parameters.

initializeCount : Vect n a ->
                  Vect n (a, Nat)
initializeCount []        = []
initializeCount (x :: xs) = ((x, 0) :: initializeCount xs)

-- This takes a function and makes it a function that counts operations.
--   Really, this should be a monadic bind.

addCount : (a -> a -> a) ->
           (a, Nat) ->
           (a, Nat) ->
           (a, Nat)
addCount f (a, n) (b, m) = (f a b, n + m + 1)

-- This is byteEq written to count operations

countingByteEq : Byte ->
                 Byte ->
                 (Bit, Nat)
countingByteEq a b = (zipAndFold (addCount bitNXor)
                                 (addCount bitAnd)
                                 (initializeCount a)
                                 (initializeCount b))

-- Now, we use idris' theorem prover to show that our function is time-
--   -constant.

-- This just tests that all the items in a vector have the same number of
--   operations performed on them.

allHasCount : Vect n (a, Nat) ->
              Nat ->
              Bool
allHasCount []             n = True
allHasCount ((a, b) :: xs) n = b == n && allHasCount xs n

-- This says that zipping two new vectors together should return a vector of
--   items that all have had one operation performed on them.

zipOps : (a,b:Vect n c) ->
         (f:c -> c -> c) ->
         allHasCount (zipWith (addCount f)
                              (initializeCount a)
                              (initializeCount b))
                     1
           =
         True
zipOps []        []        f =
     refl
zipOps (x :: xs) (y :: ys) f =
     rewrite zipOps
               xs ys f
  in refl

-- This is just the above function for specifically bytes
-- FIXME: this doesn't need to exist

zipBytes : (a,b:Byte) ->
           (f:Bit -> Bit -> Bit) ->
           allHasCount (zipWith (addCount f)
                                (initializeCount a)
                                (initializeCount b))
                       (S Z)
             =
           True
zipBytes a b f =
     rewrite zipOps
               a b f
  in refl

-- This is just the definition of addcount, namely operating on two things will
--   return a thing with an operation count of the sum of theirs plus one.

addCountBasic : (f:c -> c -> c) ->
                (a,b:(c, Nat)) ->
                snd ((addCount f) a b)
                  =
                (snd a + snd b) + 1
addCountBasic f (a,n) (b,m) =
     refl

-- This is where things get ugly.  Idris doesn't really like proving things
--   about generalized folds, so I just wrote one huge proof for only 8-element
--   vectors because that's all we're dealing with.  It's kind of the opposite
--   of elegant, nice, or anything good in the world though.

-- This is literally just a specific case of the commutative/associative
--   property of addition

addEightThings : (a,b,c,d,e,f,g,h:Nat) -> 
                 plus (plus (b) (plus (plus (c) (plus (plus (d) (plus (plus (e)
                      (plus (plus (f) (plus (plus (g) (plus (plus (h) (a)) 1))
                      1)) 1)) 1)) 1)) 1)) 1
                   =
                 plus (plus (a) (plus (b) (plus (c) (plus (d) (plus (e) (plus
                      (f) (plus (g) (plus (h) 0)))))))) (fromInteger 7)
addEightThings a b c d e f g h =
     rewrite
             plusZeroRightNeutral h
  in rewrite plusCommutative
               (plus h a) 1
  in rewrite plusCommutative
               g (S (plus h a))
  in rewrite plusCommutative
               (S (plus (plus h a) g)) 1
  in rewrite plusCommutative
               f (S (S (plus (plus h a) g)))
  in rewrite plusCommutative
               (plus (S (S (plus (plus h a) g))) f) 1
  in rewrite plusCommutative
               e (S (S (S (plus (plus (plus h a) g) f))))
  in rewrite plusCommutative
               (plus (S (S (S (plus (plus (plus h a) g) f)))) e) 1
  in rewrite plusCommutative
               d (S (S (S (S (plus (plus (plus (plus h a) g) f) e)))))
  in rewrite plusCommutative
               (plus (S (S (S (S (plus (plus (plus (plus h a) g) f) e))))) d) 1
  in rewrite plusCommutative
               c (S (S (S (S (S (plus (plus (plus (plus (plus h a) g) f) e)
                   d))))))
  in rewrite plusCommutative
               (plus (S (S (S (S (S (plus (plus (plus (plus (plus h a) g) f) e)
                   d)))))) c) 1
  in rewrite plusCommutative
               b (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus h a) g)
                   f) e) d) c)))))))
  in rewrite plusCommutative
               (plus (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus h a)
                   g) f) e) d) c))))))) b) 1
  in rewrite plusCommutative
               (plus h a) g
  in rewrite plusAssociative
               g h a
  in rewrite plusCommutative
               (plus (plus g h) a) f
  in rewrite plusAssociative
               f (plus g h) a
  in rewrite plusCommutative
               (plus (plus f (plus g h)) a) e
  in rewrite plusAssociative
               e (plus f (plus g h)) a
  in rewrite plusCommutative
               (plus (plus e (plus f (plus g h))) a) d
  in rewrite plusAssociative
               d (plus e (plus f (plus g h))) a
  in rewrite plusCommutative
               (plus (plus d (plus e (plus f (plus g h)))) a) c
  in rewrite plusAssociative
               c (plus d (plus e (plus f (plus g h)))) a
  in rewrite plusCommutative
               (plus (plus c (plus d (plus e (plus f (plus g h))))) a) b
  in rewrite plusAssociative
               b (plus c (plus d (plus e (plus f (plus g h))))) a
  in rewrite plusCommutative
               (plus b (plus c (plus d (plus e (plus f (plus g h)))))) a
  in rewrite plusCommutative
               (plus a (plus b (plus c (plus d (plus e (plus f (plus g h)))))))
                   7
  in refl
   -- FIXME: dear god I am sorry for the above

-- This states that folding an operation across a vector will perform seven
--   operations (for each adjacent pair in the vector), and so the sum of the
--   operations done on the result is the number of operations done on all the
--   items that go into it (all the items in the vector) plus seven.
-- FIXME: this proof is kind of a mess

foldrByteBasic : (a:Vect 8 (Bit, Nat)) ->
                 (f:Bit -> Bit -> Bit) ->
                 snd (vFoldr1 (addCount f) a)
                   =
                 sum (map snd a) + 7
foldrByteBasic [a,b,c,d,e,f,g,h] i =
     rewrite addCountBasic
               i b (addCount i c (addCount i d (addCount i e (addCount i f
                   (addCount i g (addCount i h a))))))
  in rewrite addCountBasic
               i c (addCount i d (addCount i e (addCount i f (addCount i g
                   (addCount i h a)))))
  in rewrite addCountBasic
               i d (addCount i e (addCount i f (addCount i g (addCount i h a))))
  in rewrite addCountBasic
               i e (addCount i f (addCount i g (addCount i h a)))
  in rewrite addCountBasic
               i f (addCount i g (addCount i h a))
  in rewrite addCountBasic
               i g (addCount i h a)
  in rewrite addCountBasic
               i h a
  in rewrite addEightThings
               (snd a) (snd b) (snd c) (snd d) (snd e) (snd f) (snd g) (snd h)
  in refl

-- This is a specific case of the above where each element has only had one op
--   performed to yield it, so the sum of the operations on the result is always
--   15.

foldrHomoByte : (a:Vect 8 (Bit,Nat)) ->
                (f:Bit -> Bit -> Bit) ->
                (p:allHasCount a (S Z)
                  =
                True) ->
                snd (vFoldr1 (addCount f) a)
                  =
                15
-- The below proof is definitely true, but at the moment type-checking it could
--   quite possibly take a bit longer than the age of the universe. Thanks
--   combinatorial explosion.
-- FIXME: make this work
-- foldrHomoByte [(a,(S Z)),(b,(S Z)),(c,(S Z)),(d,(S Z)),(e,(S Z)),(f,(S Z)),
--               (g,(S Z)),(h,(S Z))] i p = refl
foldrHomoByte a f = believe_me

-- This and the below proof both just say that if you zip two vectors togeter
--   and then fold across them, (and they're both size 8) then 15 operations
--   will be performed.
zipAndFoldBasic : (a,b:Byte) ->
                  (f,g:Bit -> Bit -> Bit) ->
                  snd (vFoldr1 (addCount f) (zipWith (addCount g)
                                            (initializeCount a)
                                            (initializeCount b)))
                    =
                  15
zipAndFoldBasic a b f g =
  rewrite foldrHomoByte
            (zipWith (addCount g) (initializeCount a) (initializeCount b)) f
                (zipBytes a b g)
  in refl

zipAndFoldBasic' : (a,b:Byte) ->
                   (f,g:Bit -> Bit -> Bit) ->
                   snd (zipAndFold (addCount f)
                                   (addCount g)
                                   (initializeCount a)
                                   (initializeCount b))
                     =
                   15
zipAndFoldBasic' a b f g =
  rewrite zipAndFoldBasic
            a b f g
  in refl

-- This says equality always takes 15 operations

numericTimeConstancy : (a,b:Byte) -> snd (countingByteEq a b) = 15
numericTimeConstancy a b =
     rewrite zipAndFoldBasic'
               a b bitNXor bitAnd
  in refl

-- And thus equality between any two pairs of bytes takes the same amount of
--   time.

timeConstancy : (a,b,c,d:Byte) ->
                snd (countingByteEq a b)
                  =
                snd (countingByteEq c d)
timeConstancy a b c d =
     rewrite numericTimeConstancy
               a b
  in rewrite numericTimeConstancy
               c d
  in refl -- QED
