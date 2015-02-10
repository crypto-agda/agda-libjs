module FFI.JS.Type where

open import FFI.JS using (JSValue; String)

data JSType : Set where
  array object number string bool null : JSType
{-# COMPILED_JS JSType function (x,v) { return require("libagda").readProp(v)(x)(); } #-}
{-# COMPILED_JS array  "array"  #-}
{-# COMPILED_JS object "object" #-}
{-# COMPILED_JS number "number" #-}
{-# COMPILED_JS string "string" #-}
{-# COMPILED_JS bool   "bool"   #-}
{-# COMPILED_JS null   "null"   #-}

postulate typeof : JSValue → JSType
{-# COMPILED_JS typeof function(x) { return typeof(x); } #-}

postulate showJSType : JSType → String
{-# COMPILED_JS showJSType String #-}

-- TODO dyn check?
postulate castJSType : String → JSType
{-# COMPILED_JS castJSType String #-}
