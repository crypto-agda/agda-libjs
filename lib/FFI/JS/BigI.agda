open import FFI.JS hiding (toString)

module FFI.JS.BigI where

abstract
  BigI : Set
  BigI = JSValue

  BigI▹JSValue : BigI → JSValue
  BigI▹JSValue x = x

  unsafe-JSValue▹BigI : JSValue → BigI
  unsafe-JSValue▹BigI x = x

postulate bigI     : (x base : String) → BigI
{-# COMPILED_JS bigI       function(x) { return function (y) { return require("bigi")(x,y); }; } #-}

postulate negate   : (x : BigI) → BigI
{-# COMPILED_JS negate     function(x) { return x.negate(); } #-}

postulate add      : (x y : BigI) → BigI
{-# COMPILED_JS add        function(x) { return function (y) { return x.add(y); }; } #-}

postulate subtract : (x y : BigI) → BigI
{-# COMPILED_JS subtract   function(x) { return function (y) { return x.subtract(y); }; } #-}

postulate multiply : (x y : BigI) → BigI
{-# COMPILED_JS multiply   function(x) { return function (y) { return x.multiply(y); }; } #-}

postulate divide   : (x y : BigI) → BigI
{-# COMPILED_JS divide     function(x) { return function (y) { return x.divide(y); }; } #-}

postulate remainder : (x y : BigI) → BigI
{-# COMPILED_JS remainder  function(x) { return function (y) { return x.remainder(y); }; } #-}

postulate mod      : (x y : BigI) → BigI
{-# COMPILED_JS mod        function(x) { return function (y) { return x.mod(y); }; } #-}

postulate modPow   : (this e m : BigI) → BigI
{-# COMPILED_JS modPow     function(x) { return function (y) { return function (z) { return x.modPow(y,z); }; }; } #-}

postulate modInv   : (this m   : BigI) → BigI
{-# COMPILED_JS modInv     function(x) { return function (y) { return x.modInverse(y); }; } #-}

postulate gcd      : (this m   : BigI) → BigI
{-# COMPILED_JS gcd        function(x) { return function (y) { return x.gcd(y); }; } #-}

-- test primality with certainty >= 1-.5^t
postulate isProbablePrime : (this : BigI)(t : Number) → Bool
{-# COMPILED_JS isProbablePrime function(x) { return function (y) { return x.isProbablePrime(y); }; } #-}

postulate signum   : (this : BigI) → Number
{-# COMPILED_JS signum function(x) { return x.signum(); } #-}

postulate equals   : (x y : BigI) → Bool
{-# COMPILED_JS equals     function(x) { return function (y) { return x.equals(y); }; } #-}

postulate compareTo : (this x : BigI) → Number
{-# COMPILED_JS compareTo  function(x) { return function (y) { return x.compareTo(y); }; } #-}

postulate toString : (x : BigI) → String
{-# COMPILED_JS toString   function(x) { return x.toString(); } #-}

postulate fromHex  : String → BigI
{-# COMPILED_JS fromHex    require("bigi").fromHex #-}

postulate toHex    : BigI → String
{-# COMPILED_JS toHex      function(x) { return x.toHex(); } #-}

postulate byteLength : BigI → Number
{-# COMPILED_JS byteLength function(x) { return x.byteLength(); } #-}

0I 1I 2I : BigI
0I = bigI "0" "10"
1I = bigI "1" "10"
2I = bigI "2" "10"

_≤I_ : BigI → BigI → Bool
x ≤I y = compareTo x y ≤Number 0N

_<I_ : BigI → BigI → Bool
x <I y = compareTo x y <Number 0N

_>I_ : BigI → BigI → Bool
x >I y = compareTo x y >Number 0N

_≥I_ : BigI → BigI → Bool
x ≥I y = compareTo x y ≥Number 0N
