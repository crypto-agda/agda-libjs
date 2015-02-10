open import FFI.JS

module FFI.JS.Properties where

-- TODO, watch out:
-- * order of keys
{-
postulate
  tofromObject : ∀ l → fromJSValue (fromObject l) ≡ object l
-}
