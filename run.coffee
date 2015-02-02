require = require "requirejs"
main    = (require process.argv[2]).main
runcmd  = (require "libagda").runJSCmd

runcmd main
