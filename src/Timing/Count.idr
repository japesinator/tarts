module Timing.Count
%default total

Count : Type -> Type
Count t = (t, Nat)

instance Functor Count where
  map f (a, n) = (f a, S n)

instance Applicative Count where
  pure a = (a, Z)
  (f, n) <$> (a, m) = (f a, S (n + m))

instance Monad Count where
  (a, n) >>= f = (fst (f a), S n)
