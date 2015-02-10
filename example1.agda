module example1 where

open import Data.String.Base using (String)
open import Data.Product
open import Data.List.Base using (List; []; _∷_)
open import Data.Bool.Base
open import Function

open import Control.Process.Type

open import FFI.JS as JS
open import FFI.JS.Proc
import FFI.JS.Console as Console
import FFI.JS.Process as Process
import FFI.JS.FS      as FS

postulate take-half : String → String
{-# COMPILED_JS take-half function(x) { return x.substring(0,x.length/2); } #-}
postulate drop-half : String → String
{-# COMPILED_JS drop-half function(x) { return x.substring(x.length/2); } #-}

test-value : Value
test-value = object (("array"  , array (array [] ∷ array (array [] ∷ []) ∷ [])) ∷
                     ("object" , array (object [] ∷ object (("a", string "b") ∷ []) ∷ [])) ∷
                     ("string" , array (string "" ∷ string "a" ∷ [])) ∷
                     ("number" , array (number zero ∷ number one ∷ [])) ∷
                     ("bool"   , array (bool true ∷ bool false ∷ [])) ∷
                     ("null"   , array (null ∷ [])) ∷ [])

test =
    fromString (JSON-stringify (fromValue test-value))
    ===
    fromString "{\"array\":[[],[[]]],\"object\":[{},{\"a\":\"b\"}],\"string\":[\"\",\"a\"],\"number\":[0,1],\"bool\":[true,false],\"null\":[null]}"


module _ {A : Set} (_≤_ : A → A → Bool) where

    merge-sort-list : (l₀ l₁ : List A) → List A
    merge-sort-list [] l₁ = l₁
    merge-sort-list l₀ [] = l₀
    merge-sort-list (x₀ ∷ l₀) (x₁ ∷ l₁) with x₀ ≤ x₁
    ... | true  = x₀ ∷ merge-sort-list l₀ (x₁ ∷ l₁)
    ... | false = x₁ ∷ merge-sort-list (x₀ ∷ l₀) l₁

merge-sort-string : String → String → String
merge-sort-string s₀ s₁ = List▹String (merge-sort-list _≤Char_ (String▹List s₀) (String▹List s₁))

mapJSArray : (JSArray String → JSArray String) → JSValue → JSValue
mapJSArray f v = fromString (onString (join "" ∘ f ∘ split "") v)

reverser : URI → JSProc
reverser d = recv d λ s → send d (mapJSArray JS.reverse s) end

adder : URI → JSProc
adder d = recv d λ s₀ → recv d λ s₁ → send d (s₀ +JS s₁) end

adder-client : URI → JSValue → JSValue → JSProc
adder-client d s₀ s₁ = send d s₀ (send d s₁ (recv d λ _ → end))

module _ (adder-addr reverser-addr : URI)(s : JSValue) where
  adder-reverser-client : JSProc
  adder-reverser-client =
    send reverser-addr s $
    send adder-addr s $
    recv reverser-addr λ rs →
    send adder-addr rs $
    recv adder-addr λ res →
    end

str-sorter₀ : URI → JSProc
str-sorter₀ d = recv d λ s → send d (mapJSArray sort s) end

str-sorter-client : ∀ {D} → D → JSValue → Proc D JSValue
str-sorter-client d s = send d s $ recv d λ _ → end

module _ (upstream helper₀ helper₁ : URI) where
  str-merger : JSProc
  str-merger =
    recv upstream λ s →
    send helper₀ (fromString (onString take-half s)) $
    send helper₁ (fromString (onString drop-half s)) $
    recv helper₀ λ ss₀ →
    recv helper₁ λ ss₁ →
    send upstream (fromString (onString (onString merge-sort-string ss₀) ss₁))
    end

dyn-merger : URI → (URI → JSProc) → JSProc
dyn-merger upstream helper =
  spawn helper λ helper₀ →
  spawn helper λ helper₁ →
  str-merger upstream helper₀ helper₁

str-sorter₁ : URI → JSProc
str-sorter₁ upstream = dyn-merger upstream str-sorter₀

str-sorter₂ : URI → JSProc
str-sorter₂ upstream = dyn-merger upstream str-sorter₁

stringifier : URI → JSProc
stringifier d = recv d λ v → send d (fromString (JSON-stringify v)) end

stringifier-client : ∀ {D} → D → JSValue → Proc D JSValue
stringifier-client d v = send d v $ recv d λ _ → end

main : JS!
main =
  Console.log "Hey!" >> assert test >>
  Process.argv !₁ λ argv → Console.log ("argv=" ++ join " " argv) >>
  Console.log "server(adder):" >> server "127.0.0.1" "1337" adder !₁ λ adder-uri →
  Console.log "client(adderclient):" >>
  client (adder-client adder-uri (fromString "Hello ") (fromString "World!")) >>
  client (adder-client adder-uri (fromString "Bonjour ") (fromString "monde!")) >>
  Console.log "server(reverser):" >>
  server "127.0.0.1" "1338" reverser !₁ λ reverser-uri →
  Console.log "client(adder-reverser-client):" >>
  client (adder-reverser-client adder-uri reverser-uri (fromString "red")) >>

  server "127.0.0.1" "1342" str-sorter₂ !₁ λ str-sorter₂-uri →
  Console.log "str-sorter-client:" >>
  client (str-sorter-client str-sorter₂-uri (fromString "Something to be sorted!")) >>

  server "127.0.0.1" "1343" stringifier !₁ λ stringifier-uri →
  client (stringifier-client stringifier-uri (fromValue test-value)) >>
  FS.readFile "README.md" nullJS !₂ λ err dat →
  Console.log ("README.md, length is " ++ Number▹String (length (castString dat))) >>
  Console.log "Bye!" >>
  end
-- -}
-- -}
-- -}
-- -}
