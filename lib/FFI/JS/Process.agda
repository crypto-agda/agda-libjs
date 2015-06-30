open import FFI.JS

module FFI.JS.Process where

-- http://nodejs.org/api/process.html#process_process_exit_code
-- postulate exit : (code : Number) → JSVoid
postulate exit : JSCmd ((code : Number) → 𝟘)
{-# COMPILED_JS exit require("libagda").process.exit #-}

-- http://nodejs.org/api/process.html#process_process_argv
postulate argv : JS[ JSArray String ]
{-# COMPILED_JS argv require("libagda").process.argv #-}
