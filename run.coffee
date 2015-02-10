require = require "requirejs"
libagda = require "libagda"
libagda.runJS (require process.argv[2]).main
