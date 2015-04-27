module FFI.JS.Console where

open import FFI.JS

postulate log : (msg : String) → JS!
{-# COMPILED_JS log require("libagda").console.log #-}
