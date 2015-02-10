module FFI.JS.Proc where

open import FFI.JS
open import Control.Process.Type

abstract
  URI = String
  showURI : URI → String
  showURI x = x
  readURI : String → URI
  readURI x = x

JSProc = Proc URI JSValue

{-
postulate server : (ip port  : String)
                   (proc     : URI → JSProc)
                   (callback : URI → JSCmd) → JSCmd
{-# COMPILED_JS server require("proc").serverCurry #-}

postulate client : JSProc → JSCmd → JSCmd
{-# COMPILED_JS client require("proc").clientCurry #-}
-}

postulate server : (ip port  : String)
                   (proc     : URI → JSProc)
                 → Callback1 URI
{-# COMPILED_JS server require("proc").serverCurry #-}

postulate client : JSProc → Callback0
{-# COMPILED_JS client require("proc").clientCurry #-}
