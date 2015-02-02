require = require "requirejs"
p       = require "proc"

double_server = (uri) ->
  p.recv uri, (msg) ->
    p.send uri, 2 * msg,
      p.end

double_client = (uri) ->
  p.send uri, 21,
    p.recv uri, (msg) ->
      console.log msg
      p.end

p.server "127.0.0.1", 3000, double_server, (uri) ->
  p.client double_client(uri), () ->
    console.log "done"
