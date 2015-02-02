module FFI.JS where

open import Data.Char.Base   public using (Char)
open import Data.String.Base public using (String)
open import Data.Bool.Base   public using (Bool; true; false)
open import Data.List.Base   using (List)
open import Data.Product     using (_×_) renaming (proj₁ to fst; proj₂ to snd)

open import Control.Process.Type

{-# COMPILED_JS Bool function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILED_JS true  true #-}
{-# COMPILED_JS false false #-}

data JSType : Set where
  array object number string bool null : JSType

infixr 5 _++_

postulate
    Number      : Set
    readNumber  : String  → Number
    zero        : Number
    one         : Number
    _+_         : Number  → Number  → Number

    _++_        : String → String → String
    reverse     : String → String
    sort        : String → String
    take-half   : String → String
    drop-half   : String → String
    String▹List : String → List Char
    List▹String : List Char → String
    Number▹String : Number → String

    JSValue        : Set
    _+JS_          : JSValue → JSValue → JSValue
    _≤JS_          : JSValue → JSValue → Bool
    _===_          : JSValue → JSValue → Bool
    JSON-stringify : JSValue → String
    JSON-parse     : String → JSValue
    toString       : JSValue → String
    fromString     : String → JSValue
    fromChar       : Char   → JSValue
    fromNumber     : Number → JSValue
    objectFromList : {A : Set} → List A → (A → String) → (A → JSValue) → JSValue
    fromJSArray    : {A : Set} → JSValue → (Number → JSValue → A) → List A
    fromJSArrayString : JSValue → List String
    castNumber     : JSValue → Number
    castString     : JSValue → String
    nullJS         : JSValue
    trueJS         : JSValue
    falseJS        : JSValue
    readJSType     : String → JSType
    showJSType     : JSType → String
    typeof         : JSValue → JSType
    _·[_]          : JSValue → JSValue → JSValue

    onString : {A : Set} (f : String → A) → JSValue → A

    trace : {A B : Set} → String → A → (A → B) → B

{-# COMPILED_JS zero      0 #-}
{-# COMPILED_JS one       1 #-}
{-# COMPILED_JS readNumber Number #-}
{-# COMPILED_JS _+_       function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _++_      function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS _+JS_     function(x) { return function(y) { return x + y; }; }  #-}
{-# COMPILED_JS reverse   function(x) { return x.split("").reverse().join(""); } #-}
{-# COMPILED_JS sort      function(x) { return x.split("").sort().join(""); }    #-}
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); }      #-}
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); }        #-}
{-# COMPILED_JS List▹String function(x) { return (require("libagda").fromList(x, function(y) { return y; })).join(""); } #-}
{-# COMPILED_JS String▹List function(x) { return require("libagda").fromJSArrayString(x.split("")); } #-}
{-# COMPILED_JS fromJSArray       function (ty) { return require("libagda").fromJSArray; } #-}
{-# COMPILED_JS fromJSArrayString require("libagda").fromJSArrayString #-}
{-# COMPILED_JS _≤JS_     function(x) { return function(y) { return x <=  y; }; } #-}
{-# COMPILED_JS _===_     function(x) { return function(y) { return x === y; }; } #-}
{-# COMPILED_JS JSON-stringify JSON.stringify #-}
{-# COMPILED_JS JSON-parse JSON.parse #-}
{-# COMPILED_JS toString   function(x) { return x.toString(); } #-}
{-# COMPILED_JS fromString function(x) { return x; } #-}
{-# COMPILED_JS fromChar   function(x) { return x; } #-}
{-# COMPILED_JS fromNumber function(x) { return x; } #-}
{-# COMPILED_JS Number▹String String #-}
{-# COMPILED_JS castNumber Number #-}
{-# COMPILED_JS castString String #-}
{-# COMPILED_JS nullJS     null #-}
{-# COMPILED_JS trueJS     true #-}
{-# COMPILED_JS falseJS    false #-}
{-# COMPILED_JS typeof     function(x) { return typeof(x); } #-}
{-# COMPILED_JS _·[_]      require("libagda").readProp #-}
{-# COMPILED_JS onString   function(t) { return require("libagda").onString; } #-}
{-# COMPILED_JS trace      require("libagda").trace #-}

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Number  → Value
  bool   : Bool → Value
  null   : Value

postulate
    fromValue : Value → JSValue

{-# COMPILED_JS fromValue require("libagda").fromValue #-}

data ValueView : Set₀ where
  array  : List JSValue → ValueView
  object : List (String × JSValue) → ValueView
  string : String → ValueView
  number : Number  → ValueView
  bool   : Bool → ValueView
  null   : ValueView

{-
postulate
    fromJSValue : JSValue → ValueView
-}

fromBool : Bool → JSValue
fromBool true  = trueJS
fromBool false = falseJS

Object = List (String × JSValue)

fromObject : Object → JSValue
fromObject o = objectFromList o fst snd

_≤Char_ : Char → Char → Bool
x ≤Char y = fromChar x ≤JS fromChar y

_≤String_ : String → String → Bool
x ≤String y = fromString x ≤JS fromString y

_≤Number_ : Number → Number → Bool
x ≤Number y = fromNumber x ≤JS fromNumber y

_·«_» : JSValue → String → JSValue
v ·« s » = v ·[ fromString s ]

abstract
  URI = String
  showURI : URI → String
  showURI x = x
  readURI : String → URI
  readURI x = x

JSProc = Proc URI JSValue

data JSCmd : Set where
  server : (ip port  : String)
           (proc     : URI → JSProc)
           (callback : URI → JSCmd) → JSCmd
  client : JSProc → JSCmd → JSCmd

  end          : JSCmd
  assert       : Bool → JSCmd → JSCmd
  console_log  : String → JSCmd → JSCmd
  process_argv : (List String → JSCmd) → JSCmd
