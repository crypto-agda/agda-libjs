define ["exports"], (libagda) ->

  fst = (x) -> x["proj₁"]
  snd = (x) -> x["proj₂"]

  id = (x) -> x
  libagda.id = id

  foldr = (a) -> (nil) -> (cons) ->
    len = a.length
    l = nil
    i = len - 1
    while i >= 0
      l = cons(i)(a[i])(l)
      i--
    l
  libagda.foldrArray  = (_A) -> (_B) -> foldr
  libagda.foldrString = (_A) ->         foldr

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

  libagda.readProp = (x) -> (y) -> (cb) ->
    z = x[y]
    if z
      cb z
    else
      throw "readProp(): undefined property #{y} for #{x}"

  libagda.viewJSValue = (v) -> (w) ->
    switch typeof(v)
      when "array"  then w.array(v)
      when "object" then w.object(v)
      when "string" then w.string(v)
      when "number" then w.number(v)
      when "bool"   then w.bool(v)
      when "null"   then w.null()
      else               w.error(v)

  libagda.checkTypeof = (ty) -> (x) -> (cb) ->
    my = typeof x
    if my is ty
      cb x
    else
      throw "checkTypeof(): expected a #{ty} not a #{my}"

  libagda.trace = (_A) -> (_B) -> (s) -> (a) -> (f) ->
    console.log "trace: #{s}#{JSON.stringify(a) || a}";
    f a

  libagda.throw = (_A) -> (s) -> (_cb) -> throw s

  libagda.catch = (_A) -> (cmd) -> (handler) -> (cb) ->
    try
      cmd(cb)
    catch error
      handler(error)(cb)

  libagda.assert = (b) -> (cb) -> throw "assert false" unless b; cb()

  libagda.process =
    exit: (code) -> (cb) -> process.exit code; cb()
    argv: (cb) -> cb process.argv

  # FFI.JS.Console.log : (msg : String) → JS!
  libagda.console =
    log: (s) -> (cb) -> console.log s; cb()

  libagda.StringToChar = (s) -> (cb) ->
    if s.length is 1
      cb s
    else
      throw "StringToChar: Expecting a string of length 1 not " + s.length

  libagda.substring  = (s) -> (i) -> (j) -> s.substring(i,j)
  libagda.substring1 = (s) -> (i) ->        s.substring(i)

  # TODO move into a libagda-fs library which can depend on fs
  libagda.fs =
    readFile: (filename) -> (options) -> (callback) -> require("fs").readFile filename, options, callback

  # _>>_ : {A : Set} → JS! → JS[ A ] → JS[ A ]
  libagda["_>>_"]  = (_A) ->                 (cmd) -> (k) -> (cb) -> cmd (_x)  -> k(cb)

  # _>>=_ : {A B : Set}(cmd : JS[ A ])(cb : A → JS[ B ]) → JS[ B ]
  libagda["_>>=_"] = (_A) -> (_B) ->         (cmd) -> (k) -> (cb) -> cmd (x)   -> k(x)(cb)

  # _=<<_ : {A B : Set}(cb : A → JS[ B ])(cmd : JS[ A ]) → JS[ B ]
  libagda["_>>=_"] = (_A) -> (_B) ->         (k)   -> (cmd) -> (cb) -> cmd (x)   -> k(x)(cb)

  # _<*>_ : {A B : Set}(cmd : JS[ A → B ])(cmd2 : JS[ A ]) → JS[ B ]
  libagda["_<*>_"] = (_A) -> (_B) ->         (cmd) -> (cmd2) -> (cb) -> cmd (f) -> cmd2 (x) -> cb(f(x))

  # _>>==_ : {A B C : Set}(cmd : JS[ A , B ])(cb : A → B → JS[ C ]) → JS[ C ]
  libagda["_>>=="] = (_A) -> (_B) -> (_C) -> (cmd) -> (k) -> (cb) -> cmd (x,y) -> k(x)(y)(cb)

  # _<=<_ : {A B C : Set}(f : B → JS[ C ])(g : A → JS[ B ]) → A → JS[ C ]
  libagda["_<=<_"] = (_A) -> (_B) -> (_C) -> (f) -> (g) -> (x) -> (cb) -> g(x) (y) -> f(y)(cb)

  # _<$>_ : {A B : Set}(f : A → B)(cmd : JS[ A ]) → JS[ B ]
  libagda["_<$>_"] = (_A) -> (_B) ->         (f) -> (cmd) -> (cb) -> cmd (x) -> cb(f(x))

  return libagda
