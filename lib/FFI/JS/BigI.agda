open import FFI.JS hiding (toString)

module FFI.JS.BigI where

abstract
  BigI : Set
  BigI = JSValue

  BigI▹JSValue : BigI → JSValue
  BigI▹JSValue x = x

  unsafe-JSValue▹BigI : BigI → JSValue
  unsafe-JSValue▹BigI x = x

postulate
  bigI     : (x base : String) → BigI
  add      : (x y : BigI) → BigI
  multiply : (x y : BigI) → BigI
  mod      : (x y : BigI) → BigI
  modPow   : (this e m : BigI) → BigI
  modInv   : (this m   : BigI) → BigI
  equals   : (x y : BigI) → Bool
  toString : (x : BigI) → String
  fromHex  : String → BigI
  toHex    : BigI → String

{-# COMPILED_JS bigI       function(x) { return function (y) { return require("bigi")(x,y); }; } #-}
{-# COMPILED_JS add        function(x) { return function (y) { return x.add(y); }; } #-}
{-# COMPILED_JS multiply   function(x) { return function (y) { return x.multiply(y); }; } #-}
{-# COMPILED_JS mod        function(x) { return function (y) { return x.mod(y); }; } #-}
{-# COMPILED_JS modPow     function(x) { return function (y) { return function (z) { return x.modPow(y,z); }; }; } #-}
{-# COMPILED_JS modInv     function(x) { return function (y) { return x.modInverse(y); }; } #-}
{-# COMPILED_JS equals     function(x) { return function (y) { return x.equals(y); }; } #-}
{-# COMPILED_JS toString   function(x) { return x.toString(); } #-}
{-# COMPILED_JS fromHex    require("bigi").fromHex #-}
{-# COMPILED_JS toHex      function(x) { return x.toHex(); } #-}

0I 1I 2I : BigI
0I = bigI "0" "10"
1I = bigI "1" "10"
2I = bigI "2" "10"
