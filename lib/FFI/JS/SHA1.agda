module FFI.JS.SHA1 where

open import Data.String.Base using (String)

postulate SHA1 : String → String
{-# COMPILED_JS SHA1 function (x) { return require("sha1")(x); } #-}
