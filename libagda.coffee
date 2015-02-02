define ["exports","proc"], (libagda,libproc) ->

  fst = (x) -> x["proj₁"]
  snd = (x) -> x["proj₂"]

  id = (x) -> x
  libagda.id = id

  foldrArray = (a, nil, cons) ->
    len = a.length
    l = nil
    i = len - 1
    while i >= 0
      l = cons i, a[i], l
      i--
    l
  libagda.foldrArray = foldrArray

  fromList = (l0, fromElt) ->
    a = []
    i = 0
    go = (l) ->
      l
        "[]":  () -> { }
        "_∷_": (x, xs) ->
                  a[i] = fromElt x
                  i++
                  go xs
    go l0
    Object.freeze a
  libagda.fromList = fromList

  objectFromList = (l0, key, val) ->
    o = {}
    go = (l) ->
      l
        "[]":  () -> { }
        "_∷_": (x, xs) ->
                o[key x] = val x
                go xs
    go l0
    Object.freeze o
  libagda.objectFromList = objectFromList

  fromValue = (v) ->
    v
      array:  (l) -> fromList l, fromValue
      object: (l) -> objectFromList l, fst, ((x) -> fromValue snd x)
      string: id
      number: id
      bool:   id
      null:   () -> null
  libagda.fromValue = fromValue

  libagda.readProp = (x) -> (y) -> x[y]

  tt   = (x) -> x.record()
  nil  = (l) -> l["[]"]()
  cons = (x, xs) -> (l) -> l["_∷_"](x, xs)
  libagda.tt = tt
  libagda.nil = nil
  libagda.cons = cons

  libagda.onString = (f) -> (x) ->
    if typeof x is "string"
      f x
    else
      throw "onString(): not a string"

  fromJSArray = (a) -> (f) -> foldrArray a, nil, (i,x,xs) -> cons ((f i) x), xs
  libagda.fromJSArray = fromJSArray

  fromJSArrayString = (a) -> (fromJSArray a) ((i) -> (x) -> String(x))
  libagda.fromJSArrayString = fromJSArrayString

  libagda.trace = (_A) -> (_B) -> (s) -> (a) -> (f) ->
    console.log "trace: #{s}#{a}";
    f a

  runJSCmd = (x) ->
    x
      server:      (ip, port, proc, cb) ->
                    libproc.server ip, port, proc, (uri) ->
                      runJSCmd cb uri
      client:      (proc, cb) -> libproc.client proc, () -> runJSCmd cb
      end:         () -> { }
      assert:      (b, cb) ->
                      throw "assert false" unless b
                      runJSCmd cb
      console_log: (s, cb) -> console.log s; runJSCmd cb
      process_argv: (cb) -> runJSCmd cb fromJSArrayString process.argv
  libagda.runJSCmd = runJSCmd

  return libagda
