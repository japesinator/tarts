import Data.Vect

-- We can represent state as a list of String, Nat pairs, each of which
--   represents a register, and then represent time as a vector, where each
--   element is the state at a given time
runInstruction : (List (String, Nat) -> List (String, Nat))
              -> Vect (S n)     (List (String, Nat))
              -> Vect (S n + 1) (List (String, Nat))
runInstruction f v = v ++ [f $ last v]

-- Then, we just extract the length of the vector to get time elapsed
time : {n : Nat} -> Vect (S n) (List (String, Nat)) -> Nat
time {n} _ = S n
