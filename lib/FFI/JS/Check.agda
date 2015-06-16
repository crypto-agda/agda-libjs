{-# OPTIONS --without-K #-}
module FFI.JS.Check where

open import FFI.JS
import FFI.JS.Console as Console

check : {A : Set}(pred : Bool)(errmsg : 𝟙 → String)(input : A) → A
check true  errmsg x = x
check false errmsg x = throw (errmsg _) x

warn-check : {A : Set}(pred : Bool)(errmsg : 𝟙 → String)(input : A) → A
warn-check true  errmsg x = x
warn-check false errmsg x = trace ("Warning: " ++ errmsg _) x (λ y → y)

check! : (title  : String)
         (pred   : Bool)
         (errmsg : 𝟙 → String)
       → JS!
check! title true  errmsg = Console.log (title ++ ": PASS")
check! title false errmsg = Console.log (title ++ ": FAIL [" ++ errmsg _ ++ "]")
