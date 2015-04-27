module FFI.JS.FS where

open import FFI.JS

{-
TODO:

* Is the use of String always correct here?
* A raw JSValue for options is not really nice
* Depending on the presence of the encoding option the result is either a String or a Buffer.
-}

-- http://nodejs.org/api/fs.html#fs_fs_readfile_filename_options_callback
postulate readFile : (filename : String)(options : JSValue)
                   → JSCmd (((err : JSValue)(dat : JSValue) → 𝟘) → 𝟘)
{-# COMPILED_JS readFile require("libagda").fs.readFile #-}

  -- To some extent the JSCmd should be a monad for this kind of things.
  -- readFileSync : (filename : String)(options : JSValue) → TODO JSValue
