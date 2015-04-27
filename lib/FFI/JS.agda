module FFI.JS where

open import Data.Empty       public renaming (⊥ to 𝟘)
open import Data.Unit.Base   public renaming (⊤ to 𝟙)
open import Data.Char.Base   public using (Char)
open import Data.String.Base public using (String)
open import Data.Bool.Base   public using (Bool; true; false)
open import Data.List.Base   using (List; []; _∷_)
open import Data.Product     using (_×_) renaming (proj₁ to fst; proj₂ to snd)
open import Function         using (id; _∘_)

open import Control.Process.Type

{-# COMPILED_JS Bool function (x,v) { return ((x)? v["true"]() : v["false"]()); } #-}
{-# COMPILED_JS true  true #-}
{-# COMPILED_JS false false #-}

postulate
  Number   : Set
  JSArray  : Set → Set
  JSObject : Set
  JSValue  : Set

postulate readNumber : String → Number
{-# COMPILED_JS readNumber Number #-}

postulate 0N : Number
{-# COMPILED_JS 0N 0 #-}

postulate 1N : Number
{-# COMPILED_JS 1N 1 #-}

postulate 2N : Number
{-# COMPILED_JS 2N 2 #-}

postulate 4N : Number
{-# COMPILED_JS 4N 4 #-}

postulate 8N : Number
{-# COMPILED_JS 8N 8 #-}

postulate 16N : Number
{-# COMPILED_JS 16N 16 #-}

postulate 32N : Number
{-# COMPILED_JS 32N 32 #-}

postulate 64N : Number
{-# COMPILED_JS 64N 64 #-}

postulate 128N : Number
{-# COMPILED_JS 128N 128 #-}

postulate 256N : Number
{-# COMPILED_JS 256N 256 #-}

postulate 512N : Number
{-# COMPILED_JS 512N 512 #-}

postulate 1024N : Number
{-# COMPILED_JS 1024N 1024 #-}

postulate 2048N : Number
{-# COMPILED_JS 2048N 2048 #-}

postulate 4096N : Number
{-# COMPILED_JS 4096N 4096 #-}

postulate _+_ : Number → Number → Number
{-# COMPILED_JS _+_ function(x) { return function(y) { return x + y; }; } #-}

postulate _−_ : Number → Number → Number
{-# COMPILED_JS _−_ function(x) { return function(y) { return x - y; }; } #-}

postulate _*_ : Number → Number → Number
{-# COMPILED_JS _*_ function(x) { return function(y) { return x * y; }; } #-}

postulate _/_ : Number → Number → Number
{-# COMPILED_JS _/_ function(x) { return function(y) { return x / y; }; } #-}

infixr 5  _++_
postulate _++_ : String → String → String
{-# COMPILED_JS _++_ function(x) { return function(y) { return x + y; }; } #-}

postulate _+JS_ : JSValue → JSValue → JSValue
{-# COMPILED_JS _+JS_ function(x) { return function(y) { return x + y; }; } #-}

postulate _≤JS_ : JSValue → JSValue → Bool
{-# COMPILED_JS _≤JS_ function(x) { return function(y) { return x <= y; }; } #-}

postulate _<JS_ : JSValue → JSValue → Bool
{-# COMPILED_JS _<JS_ function(x) { return function(y) { return x < y; }; } #-}

postulate _>JS_ : JSValue → JSValue → Bool
{-# COMPILED_JS _>JS_ function(x) { return function(y) { return x > y; }; } #-}

postulate _≥JS_ : JSValue → JSValue → Bool
{-# COMPILED_JS _≥JS_ function(x) { return function(y) { return x >= y; }; } #-}

postulate _===_ : JSValue → JSValue → Bool
{-# COMPILED_JS _===_ function(x) { return function(y) { return x === y; }; } #-}

postulate reverse : {A : Set} → JSArray A → JSArray A
{-# COMPILED_JS reverse function(ty) { return function(x) { return x.reverse(); }; } #-}

postulate sort : {A : Set} → JSArray A → JSArray A
{-# COMPILED_JS sort function(ty) { return function(x) { return x.sort(); }; } #-}

postulate split : (sep target : String) → JSArray String
{-# COMPILED_JS split function(sep) { return function(target) { return target.split(sep); }; } #-}

postulate join : (sep : String)(target : JSArray String) → String
{-# COMPILED_JS join function(sep) { return function(target) { return target.join(sep); }; } #-}

postulate fromList : {A B : Set}(xs : List A)(fromElt : A → B) → JSArray B
{-# COMPILED_JS fromList require("libagda").fromList #-}

postulate length : String → Number
{-# COMPILED_JS length function(s) { return s.length; } #-}

postulate JSON-stringify : JSValue → String
{-# COMPILED_JS JSON-stringify JSON.stringify #-}

postulate JSON-parse : String → JSValue
{-# COMPILED_JS JSON-parse JSON.parse #-}

postulate toString : JSValue → String
{-# COMPILED_JS toString function(x) { return x.toString(); } #-}

postulate fromBool : Bool → JSValue
{-# COMPILED_JS fromBool function(x) { return x; } #-}

postulate fromString : String → JSValue
{-# COMPILED_JS fromString function(x) { return x; } #-}

postulate fromChar : Char → JSValue
{-# COMPILED_JS fromChar String #-}

postulate Char▹String : Char → String
{-# COMPILED_JS Char▹String String #-}

postulate fromNumber : Number → JSValue
{-# COMPILED_JS fromNumber function(x) { return x; } #-}

postulate fromJSArray : {A : Set} → JSArray A → JSValue
{-# COMPILED_JS fromJSArray function(ty) { return function(x) { return x; }; } #-}

postulate fromJSObject : JSObject → JSValue
{-# COMPILED_JS fromJSObject function(x) { return x; } #-}

postulate objectFromList : {A : Set}(xs : List A)(fromKey : A → String)(fromVal : A → JSValue) → JSObject
{-# COMPILED_JS objectFromList require("libagda").objectFromList #-}

postulate decodeJSArray : {A B : Set}(arr : JSArray A)(fromElt : Number → A → B) → List B
{-# COMPILED_JS decodeJSArray require("libagda").decodeJSArray #-}

postulate castNumber : JSValue → Number
{-# COMPILED_JS castNumber Number #-}

postulate castString : JSValue → String
{-# COMPILED_JS castString String #-}

-- TODO dyn check of length 1?
postulate castChar : JSValue → Char
{-# COMPILED_JS castChar String #-}

-- TODO dyn check of length 1?
postulate String▹Char : String → Char
{-# COMPILED_JS String▹Char String #-}

-- TODO dyn check?
postulate castJSArray : JSValue → JSArray JSValue
{-# COMPILED_JS castJSArray function(x) { return x; } #-}

-- TODO dyn check?
postulate castJSObject : JSValue → JSObject
{-# COMPILED_JS castJSObject function(x) { return x; } #-}

postulate nullJS : JSValue
{-# COMPILED_JS nullJS null #-}

postulate _·[_] : JSValue → JSValue → JSValue
{-# COMPILED_JS _·[_] require("libagda").readProp #-}

postulate _Array[_] : {A : Set} → JSArray A → Number → A
{-# COMPILED_JS _Array[_] function(ty) { return require("libagda").readProp; } #-}

postulate onJSArray : {A : Set} (f : JSArray JSValue → A) → JSValue → A
{-# COMPILED_JS onJSArray require("libagda").onJSArray #-}

postulate onString : {A : Set} (f : String → A) → JSValue → A
{-# COMPILED_JS onString require("libagda").onString #-}

-- Writes 'msg' and 'inp' to the console and then returns `f inp`
postulate trace : {A B : Set}(msg : String)(inp : A)(f : A → B) → B
{-# COMPILED_JS trace require("libagda").trace #-}

postulate throw : {A : Set} → String → A → A
{-# COMPILED_JS throw require("libagda").throw #-}

data Value : Set₀ where
  array  : List Value → Value
  object : List (String × Value) → Value
  string : String → Value
  number : Number → Value
  bool   : Bool   → Value
  null   : Value

Object = List (String × JSValue)

postulate fromValue : Value → JSValue
{-# COMPILED_JS fromValue require("libagda").fromValue #-}

-- TODO we could make it a COMPILED type and remove the encoding by using JSValue as the internal repr.
data ValueView : Set₀ where
  array  : JSArray JSValue → ValueView
  object : JSObject        → ValueView
  string : String          → ValueView
  number : Number          → ValueView
  bool   : Bool            → ValueView
  null   : ValueView

-- TODO not yet tested
postulate viewJSValue : JSValue → ValueView
{-# COMPILED_JS viewJSValue require("libagda").viewJSValue #-}

Bool▹String : Bool → String
Bool▹String true  = "true"
Bool▹String false = "false"

List▹String : List Char → String
List▹String xs = join "" (fromList xs Char▹String)

String▹List : String → List Char
String▹List s = decodeJSArray (split "" s) (λ _ → String▹Char)

Number▹String : Number → String
Number▹String = castString ∘ fromNumber

JSArray▹ListString : {A : Set} → JSArray A → List A
JSArray▹ListString a = decodeJSArray a (λ _ → id)

fromObject : Object → JSObject
fromObject o = objectFromList o fst snd

_≤Char_ : Char → Char → Bool
x ≤Char y = fromChar x ≤JS fromChar y

_<Char_ : Char → Char → Bool
x <Char y = fromChar x <JS fromChar y

_>Char_ : Char → Char → Bool
x >Char y = fromChar x >JS fromChar y

_≥Char_ : Char → Char → Bool
x ≥Char y = fromChar x ≥JS fromChar y

_≤String_ : String → String → Bool
x ≤String y = fromString x ≤JS fromString y

_<String_ : String → String → Bool
x <String y = fromString x <JS fromString y

_>String_ : String → String → Bool
x >String y = fromString x >JS fromString y

_≥String_ : String → String → Bool
x ≥String y = fromString x ≥JS fromString y

_≤Number_ : Number → Number → Bool
x ≤Number y = fromNumber x ≤JS fromNumber y

_<Number_ : Number → Number → Bool
x <Number y = fromNumber x <JS fromNumber y

_>Number_ : Number → Number → Bool
x >Number y = fromNumber x >JS fromNumber y

_≥Number_ : Number → Number → Bool
x ≥Number y = fromNumber x ≥JS fromNumber y

_·«_» : JSValue → String → JSValue
v ·« s » = v ·[ fromString s ]

_·«_»A : JSValue → String → JSArray JSValue
v ·« s »A = castJSArray (v ·« s »)

trace-call : {A B : Set} → String → (A → B) → A → B
trace-call s f x = trace s (f x) id

postulate JSCmd : Set → Set

Callback1 : Set → Set
Callback1 A = JSCmd ((A → 𝟘) → 𝟘)

Callback0 : Set
Callback0 = Callback1 𝟙

Callback2 : Set → Set → Set
Callback2 A B = JSCmd ((A → B → 𝟘) → 𝟘)

postulate assert : Bool → Callback0
{-# COMPILED_JS assert require("libagda").assert #-}

check : {A : Set}(pred : Bool)(errmsg : 𝟙 → String)(input : A) → A
check true  errmsg x = x
check false errmsg x = throw (errmsg _) x

warn-check : {A : Set}(pred : Bool)(errmsg : 𝟙 → String)(input : A) → A
warn-check true  errmsg x = x
warn-check false errmsg x = trace ("Warning: " ++ errmsg _) x id

infixr 0  _>>_ _!₁_ _!₂_
data JS! : Set₁ where
  end  : JS!
  _!₁_ : {A : Set}(cmd : Callback1 A)(cb : A → JS!) → JS!
  _!₂_ : {A B : Set}(cmd : JSCmd ((A → B → 𝟘) → 𝟘))(cb : A → B → JS!) → JS!

_>>_ : Callback0 → JS! → JS!
cmd >> cont = cmd !₁ λ _ → cont
-- -}
-- -}
-- -}
-- -}
-- -}
