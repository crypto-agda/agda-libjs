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
  JSCmd    : Set → Set

JS[_] : Set → Set
JS[ A ] = JSCmd ((A → 𝟘) → 𝟘)

-- Old name
Callback1 = JS[_]

JS! : Set
JS! = JS[ 𝟙 ]

JS[_,_] : Set → Set → Set
JS[ A , B ] = JSCmd ((A → B → 𝟘) → 𝟘)

Callback2 = JS[_,_]

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

postulate substring : String → Number → Number → String
{-# COMPILED_JS substring require("libagda").substring #-}

-- substring with only one argument provided
postulate substring1 : String → Number → String
{-# COMPILED_JS substring1 require("libagda").substring1 #-}

postulate String▹JSArray : String → JSArray Char
{-# COMPILED_JS String▹JSArray function(s) { return s.split(""); } #-}

postulate JSArray▹String : JSArray Char → String
{-# COMPILED_JS JSArray▹String function(a) { return a.join(""); } #-}

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
{-# COMPILED_JS fromJSArray function(A) { return function(x) { return x; }; } #-}

postulate fromJSObject : JSObject → JSValue
{-# COMPILED_JS fromJSObject function(x) { return x; } #-}

postulate fromAny : {A : Set} → A → JSValue
{-# COMPILED_JS fromAny function(A) { return function(x) { return x; }; } #-}

postulate objectFromList : {A : Set}(xs : List A)(fromKey : A → String)(fromVal : A → JSValue) → JSObject
{-# COMPILED_JS objectFromList require("libagda").objectFromList #-}

postulate foldrArray : {A B : Set}(arr : JSArray A)(nil : B)(cons : Number → A → B → B) → B
{-# COMPILED_JS foldrArray require("libagda").foldrArray #-}

postulate foldrString : {A : Set}(s : String)(nil : A)(cons : Number → Char → A → A) → A
{-# COMPILED_JS foldrString require("libagda").foldrString #-}

postulate String▹Char : String → JS[ Char ]
{-# COMPILED_JS String▹Char require("libagda").StringToChar #-}

postulate checkTypeof : (type : String) → JSValue → JS[ JSValue ]
{-# COMPILED_JS checkTypeof require("libagda").checkTypeof #-}

postulate castNumber : JSValue → JS[ Number ]
{-# COMPILED_JS castNumber require("libagda").checkTypeof("number") #-}

postulate castString : JSValue → JS[ String ]
{-# COMPILED_JS castString require("libagda").checkTypeof("string") #-}

postulate castJSArray : JSValue → JS[ JSArray JSValue ]
{-# COMPILED_JS castJSArray require("libagda").checkTypeof("array") #-}

postulate castJSObject : JSValue → JS[ JSObject ]
{-# COMPILED_JS castJSObject require("libagda").checkTypeof("object") #-}

postulate castBool : JSValue → JS[ Bool ]
{-# COMPILED_JS castBool require("libagda").checkTypeof("bool") #-}

postulate nullJS : JSValue
{-# COMPILED_JS nullJS null #-}

postulate undefinedJS : JSValue
{-# COMPILED_JS undefinedJS undefined #-}

postulate _·[_] : JSValue → JSValue → JS[ JSValue ]
{-# COMPILED_JS _·[_] require("libagda").readProp #-}

postulate _Array[_] : {A : Set} → JSArray A → Number → JS[ A ]
{-# COMPILED_JS _Array[_] function(ty) { return require("libagda").readProp; } #-}

-- Writes 'msg' and 'inp' to the console and then returns `f inp`
postulate trace : {A B : Set}(msg : String)(inp : A)(f : A → B) → B
{-# COMPILED_JS trace require("libagda").trace #-}

-- Same type as trace but does not print anything
-- Usage:
--   open import FFI.JS renaming (no-trace to trace)
no-trace : {A B : Set}(msg : String)(inp : A)(f : A → B) → B
no-trace _ inp f = f inp

postulate is-null : JSValue → Bool
{-# COMPILED_JS is-null function(x) { return (x == null); } #-}

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
  error  : JSValue         → ValueView

-- TODO not yet tested
postulate viewJSValue : JSValue → ValueView
{-# COMPILED_JS viewJSValue require("libagda").viewJSValue #-}

postulate assert : Bool → JS!
{-# COMPILED_JS assert require("libagda").assert #-}

postulate return : {A : Set}(x : A) → JS[ A ]
{-# COMPILED_JS return function(A) { return function(x) { return function(cb) { return cb(x); }; }; } #-}

{- Note about _>>_, _>>=_ and _>>==_, instead of using the corresponding functions
   from libagda. It's preferable to inline their definitions as compiled
   statements. The reason is that these COMPILED_JS statements uses a call-by-name
   semantics with strong reduction.

   The worse is for _>>_ which would have a poor run-time semantics,
   where the second command is needlessly computed.
   Worse given the use of partial functions which would still pretend to be pure
   at the type level, ... this can lead to abort the program.
-}

infixr 1 _=<<_ _>>==_ _<=<_ -- _>=>_
infixl 1 _>>=_ _>>_
infixl 4 _<$>_ _<*>_

postulate _>>=_ : {A B : Set}(cmd : JS[ A ])(cb : A → JS[ B ]) → JS[ B ]
{-# COMPILED_JS _>>=_ function(A) { return function(B) { return function(cmd) { return function(k) { return function(cb) { return cmd(function(x) { return k(x)(cb); }); }; }; }; }; } #-}

postulate _=<<_ : {A B : Set}(cb : A → JS[ B ])(cmd : JS[ A ]) → JS[ B ]
{-# COMPILED_JS _=<<_ function(A) { return function(B) { return function(k) { return function(cmd) { return function(cb) { return cmd(function(x) { return k(x)(cb); }); }; }; }; }; } #-}

postulate _<=<_ : {A B C : Set}(f : B → JS[ C ])(g : A → JS[ B ]) → A → JS[ C ]
{-# COMPILED_JS _<=<_ function(A) { return function(B) { return function(C) { return function(f) { return function(g) { return function(x) { return function(cb) { return g(x)(function(y) { return f(y)(cb); }); }; }; }; }; }; }; } #-}

postulate _<$>_ : {A B : Set}(f : A → B)(cmd : JS[ A ]) → JS[ B ]
{-# COMPILED_JS _<$>_ function(A) { return function(B) { return function(f) { return function(cmd) { return function(cb) { return cmd(function(x) { return cb(f(x)); }); }; }; }; }; } #-}

postulate _<*>_ : {A B : Set}(f : JS[ (A → B) ])(cmd : JS[ A ]) → JS[ B ]
{-# COMPILED_JS _<*>_ function(A) { return function(B) { return function(cmd) { return function(cmd2) { return function(cb) { return cmd(function(f) { return cmd2(function(x) { return cb(f(x)); }); }); }; }; }; }; } #-}

postulate _>>==_ : {A B C : Set}(cmd : JS[ A , B ])(cb : A → B → JS[ C ]) → JS[ C ]
{-# COMPILED_JS _>>==_ function(A) { return function(B) { return function(C) { return function(cmd) { return function(k) { return function(cb) { return cmd(function(x, y) { return k(x)(y)(cb); }); }; }; }; }; }; } #-}

postulate _>>_ : {A : Set} → JS! → JS[ A ] → JS[ A ]
{-# COMPILED_JS _>>_ function(A) { return function(cmd) { return function(k) { return function(cb) { return cmd(function(x) { return k(cb); }); }; }; }; } #-}

postulate throw : {A : Set} → String → A → JS[ A ]
{-# COMPILED_JS throw require("libagda").throw #-}

postulate catch : {A : Set} → JS[ A ] → (String → JS[ A ]) → JS[ A ]
{-# COMPILED_JS catch require("libagda").catch #-}

decodeJSArray : {A B : Set}(arr : JSArray A)(fromElt : Number → A → B) → List B
decodeJSArray arr fromElt = foldrArray arr [] (λ i x xs → fromElt i x ∷ xs)

sequence : {A : Set} → List JS[ A ] → JS[ List A ]
sequence []       = return []
sequence (x ∷ xs) = (_∷_ <$> x) <*> sequence xs

Bool▹String : Bool → String
Bool▹String true  = "true"
Bool▹String false = "false"

List▹String : List Char → String
List▹String xs = join "" (fromList xs Char▹String)

String▹List : String → List Char
String▹List s = foldrString s [] (λ _ → _∷_)

Number▹String : Number → String
Number▹String = toString ∘ fromNumber

JSArray▹List : {A : Set} → JSArray A → List A
JSArray▹List a = decodeJSArray a (λ _ → id)

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

trace-call : {A B : Set} → String → (A → B) → A → B
trace-call s f x = trace s (f x) id

_·«_» : JSValue → String → JS[ JSValue ]
v ·« s » = v ·[ fromString s ]

_·«_»A : JSValue → String → JS[ JSArray JSValue ]
v ·« s »A = castJSArray =<< v ·« s »

castChar : JSValue → JS[ Char ]
castChar = String▹Char <=< castString

-- -}
-- -}
-- -}
-- -}
-- -}
