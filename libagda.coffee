define ["exports"], (libagda) ->

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
  libagda.fromList = (_A) -> (_B) -> (l) -> (fromElt) -> fromList l, fromElt

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
  libagda.objectFromList = (_A) -> (l) -> (key) -> (val) -> objectFromList l, key, val

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

  libagda.viewJSValue = (v) -> (w) ->
    switch typeof(v)
      when "array"  then w.array(v)
      when "object" then w.object(v)
      when "string" then w.string(v)
      when "number" then w.number(v)
      when "bool"   then w.bool(v)
      when "null"   then w.null()
      else throw "viewJSValue: IMPOSSIBLE"

  libagda.checkTypeof = (ty) -> (x) ->
    my = typeof x
    if my is ty
      x
    else
      throw "checkTypeof(): expected a #{ty} not a #{my}"

  libagda.decodeJSArray = (_A) -> (_B) -> (a) -> (f) ->
    foldrArray a, nil, (i,x,xs) -> cons ((f i) x), xs

  libagda.trace = (_A) -> (_B) -> (s) -> (a) -> (f) ->
    console.log "trace: #{s}#{a}";
    f a

  libagda.throw = (_A) -> (s) -> (_x) -> throw s

  libagda.assert = (b) -> (cb) -> throw "assert false" unless b; cb()

  libagda.process =
    exit: (code) -> (cb) -> process.exit code; cb()
    argv: (cb) -> cb(process.argv)

  # FFI.JS.Console.log : (msg : String) → Callback0
  libagda.console =
    log: (s) -> (cb) -> console.log s; cb()

  libagda.StringToChar = (s) ->
    if s.length is 1
      s
    else
      throw "StringToChar: Expecting a string of length 1 not " + s.length

  # TODO move into a libagda-fs library which can depend on fs
  libagda.fs =
    readFile: (filename) -> (options) -> (callback) -> require("fs").readFile filename, options, callback

  # call1 : {A : Set}(cmd : Callback1 A)(cb : A → JS!) → JS!
  libagda.call1 = (_A) ->         (cmd) -> (k) -> (cb) -> cmd (x)   -> k(x)(cb)
  # call2 : {A B : Set}(cmd : JSCmd ((A → B → 𝟘) → 𝟘))(cb : A → B → JS!) → JS!
  libagda.call2 = (_A) -> (_B) -> (cmd) -> (k) -> (cb) -> cmd (x,y) -> k(x)(y)(cb)

  return libagda
