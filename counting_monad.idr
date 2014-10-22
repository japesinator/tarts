Count : Type -> Type
Count t = (t, Nat)

instance Functor Count where
  map f (a, n) = (f a, n + 1)

instance Applicative Count where
  pure a = (a, 0)
  (f, n) <$> (a, m) = (f a, n + m + 1)

instance Monad Count where
  (a, n) >>= f = (fst (f a), n + 1)
