# This module defines an execution engine for objects
# following the Agda type JSProc.
# In the following the type URI is String and the type
# JSValue is any JSValue which can be JSON encoded.
#
# ###############
# ## Interface ##
# ###############
#
# Here are the exported functions to consume processes:
#
# # Start a server with the given process
# server : (ip       : String,
#           port     : String,
#           proc     : URI → JSProc,
#           callback : URI → a) → a
#
# # Start a client with the given process
# client : (proc     : JSProc,
#           callback : () → a) → a
#
# Here are the exported functions to build processes:
#
# # A process which sends the message (msg), to the process
# # at URI (uri), and then proceed as the process (proc)
# send : (uri : URI, msg : JSValue, proc : JSProc) → JSProc
#
# # A process which receives from the process at URI (uri),
# # a message given to the process (proc)
# recv : (uri : URI, proc : (msg : JSValue) → JSProc) → JSProc
#
# # A process which ends
# end : () → JSProc
#
# # A process which create a bidirectional channel and
# # spawns two sub processes, each receiving one side
# # of this channel.
# spawn : (proc0 : (uri : URI) → JSProc,
#          proc1 : (uri : URI) → JSProc) → JSProc
#
# # A process which fails with the given error message (err)
# error : (err : String) → JSProc
#
# serverCurry and clientCurry are curry versions of server and client
#
# #############
# ## Example ##
# #############
#
# For instance here is a process reading a number 'n' and sending
# back the number 2*n:
#
# p = require "proc"
#
# double_server = (uri) ->
#   p.recv uri, (msg) ->
#     p.send uri, 2 * msg,
#       p.end
#
# double_client = (uri) ->
#   p.send uri, 21,
#     p.recv uri, (msg) ->
#       p.end
#
# ###############
# ## Internals ##
# ###############
#
# p.server "127.0.0.1", 3000, double_server, (uri) ->
#   p.client double_client(uri), () ->
#     console.log "done"
#
# However this module is made to run processes extracted
# from Agda code. This module can be used independently.
# Internally a process corresponds to the extraction of
# the type from Control.Process.Type, namely any function
# making use the given constructors:
#
# JSProc =
#   { end   : () → a
#   , send  : (uri : URI, msg : JSValue, proc : a) → a
#   , recv  : (uri : URI, proc : JSValue → a) → a
#   , spawn : (proc0 : (uri : URI) → a,
#              proc1 : (uri : URI) → a) → a
#   , error : (err : String) → a
#   } → a
define ["exports"
       ,"request"
       ,"http"
       ,"sha256"
       ,"crypto"],
       (exports
       ,request
       ,http
       ,sha256
       ,crypto) ->

  fresh_port = 20000 # we hope is fresh
  next_port = () -> ++fresh_port

  localIP = "127.0.0.1"
  upstreamURI = "upstream://"

  post = (tokens, dest, query, cb) ->
    h = {}
    token = tokens[dest]
    h.token = token if token
    h.query = query if query
    request.post {uri: dest, json: h}, (error, response, body) ->
      throw error if error
      if response.statusCode isnt 200
        throw "Unexpected status code: #{response.statusCode}. Body: #{body}"
      else
        tokens[dest] = body.token
        cb body.response

  # Spawning is shared between servers and clients.
  # While in theory this should be symmetric (switching proc0 and proc1).
  # Here we have proc0 to return a 'Proc' and proc1 to be a 'JSCmd'.
  spawn = (me, cb, proc0, proc1) ->
    console.log "[#{me}] spawns two new processes"
    # TODO deallocate servers
    newPort = next_port()
    server localIP, newPort, proc0, (newURI) ->
      cb proc1 newURI

  # server : (ip       : String,
  #           port     : String,
  #           proc     : URI → JSProc,
  #           callback : URI → a) → a
  server = (ip, port, init_server, callback) ->

    server_tokens = {}
    client_tokens = {}
    server_token_num = 0
    random_seed = crypto.randomBytes 32
    console.log "sha256.x2(random_seed): " + sha256.x2 random_seed
    uri = "http://#{ip}:#{port}/"

    new_token = (cb) ->
      token = sha256.x2 "#{random_seed}:#{server_token_num++}"
      # console.log("token: " + token)
      server_tokens[token] =
        callback: cb
        token:    token
      # TODO timestamp/expiration
      # setTimeout(cb, ms)
      token

    handle_request = (req, res) ->

      err = (code, msg) ->
        res.writeHead code
        res.end msg

      ok = (msg) ->
        s = JSON.stringify msg
        res.writeHead 200,
            "content-length": s.length
            "content-type":   "application/json"
        res.end s

      body = ""
      query = null

      recv = (d, k) ->
        if d is upstreamURI
          if query
            console.log "[#{uri}] server receives: #{JSON.stringify query}"
            ok
              token: new_token k query
          else
            err 400, "[#{uri}] server wants to receive: a query field was expected"
        else
          if query
            # TODO better error message
            err 400, "[#{uri}] server wants to receive: a query field was NOT expected"
          else
            console.log "[#{uri}] server needs a query from dest: #{d}"
            post client_tokens, d, null, (resp) ->
              go k resp

      send = (d, msg, k) ->
        if query
          err 400, "server wants to send: no query field was expected"
        else if d is upstreamURI
          console.log "[#{uri}] server sends: #{JSON.stringify msg}"
          ok
            token:    new_token k
            response: msg
        else
          console.log "[#{uri}] server sends: #{JSON.stringify msg} to: #{d}"
          post client_tokens, d, msg, (resp) -> go k

      end = () ->
        err 400, "server already ended the protocol"

      error = (msg) -> err 400, msg

      go = (x) ->
        x
          recv:  recv
          send:  send
          end:   end
          error: error
          spawn: (p0, p1) -> spawn uri, go, p0, p1

      if req.method is "POST"

        req.on "data", (chunk) -> body += chunk

        req.on "end", () ->
          body = JSON.parse body

          if body
            query = body.query

            if body.token
              # token present in request
              session = server_tokens[body.token]
              if session # valid token
                go session.callback
              else
                err 404, "invalid token"
            else
              # no token, initialize
              go init_server upstreamURI
          else
            err 400, "invalid JSON body"

      else
        err 404, "not a POST"

    http_server = http.createServer handle_request
    http_server.listen port, ip
    console.log "[#{uri}] server running"
    callback uri

  # client : (proc     : JSProc,
  #           callback : () → a) → a
  client = (client_init, cb) ->
    tokens = {}
    recv = (dest, k) ->
      post tokens, dest, null, (resp) ->
        console.log "client receives: #{JSON.stringify resp} from: #{dest}"
        go k resp

    send = (dest, query, k) ->
      console.log "client sends: #{JSON.stringify query} to: #{dest}"
      post tokens, dest, query, (resp) -> go k

    end = () ->
      console.log "client ends"
      cb()

    error = (msg) -> err 400, msg

    go = (x) ->
      x
        recv:  recv
        send:  send
        end:   end
        error: error
        spawn: (p0,p1) -> spawn "client", go, p0, p1

    go client_init

  exports.server = server
  exports.client = client
  exports.end    = () -> (p) -> p.end
  exports.send   = (uri, msg, proc) -> (p) -> p.send(uri, msg, proc)
  exports.recv   = (uri, proc) -> (p) -> p.recv(uri, proc)
  exports.spawn  = (proc0, proc1) -> (p) -> p.spawn(proc0, proc1)
  exports.error  = (err) -> (p) -> p.error(err)

  exports.serverCurry = (ip) -> (port) -> (proc) -> (callback) -> server ip, port, proc, callback
  exports.clientCurry = (proc) -> (callback) -> client proc, callback
  exports
