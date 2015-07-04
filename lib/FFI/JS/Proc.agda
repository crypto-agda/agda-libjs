module FFI.JS.Proc where

open import FFI.JS
open import Control.Process.Type

postulate URI : Set

postulate showURI : URI → String
{-# COMPILED_JS showURI function(x) { return x; } #-}

postulate readURI : String → URI
{-# COMPILED_JS readURI function(x) { return x; } #-}

JSProc = Proc URI JSValue

{-
postulate server : (ip port  : String)
                   (proc     : URI → JSProc)
                   (callback : URI → JS!) → JS!
{-# COMPILED_JS server require("proc").serverCurry #-}

postulate client : JSProc → JS! → JS!
{-# COMPILED_JS client require("proc").clientCurry #-}
-}

postulate server : (ip port  : String)
                   (proc     : URI → JSProc)
                 → JS[ URI ]
{-# COMPILED_JS server require("proc").serverCurry #-}

postulate client : JSProc → JS!
{-# COMPILED_JS client require("proc").clientCurry #-}
