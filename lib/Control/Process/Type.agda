{-
  On the one hand this module has nothing to do with JS, on the other
  hand our JS binding relies on this particular type definition.
-}
module Control.Process.Type where

open import Data.String.Base using (String)

data Proc (C {-channels-} : Set₀) (M {-messages-} : Set₀) : Set₀ where
  end   : Proc C M
  send  : (d : C) (m : M) (p : Proc C M) → Proc C M
  recv  : (d : C) (p : M → Proc C M) → Proc C M
  spawn : (p : C → Proc C M)
          (q : C → Proc C M) → Proc C M
  error : (err : String) → Proc C M
