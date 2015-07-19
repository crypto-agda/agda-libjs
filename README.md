agda-libjs
==========

Core bindings to run Agda code using NodeJS.

The module `proc.coffee` is actually independent from Agda.

Dependencies
------------

Make sure you have nodejs installed.

Then one way install CoffeeScript is to use npm:

```
npm install -g coffee-script
```

Finally to run the example you need these two packages:

```
npm install request sha256 requirejs
```

Compiling the library and running the example can be done as follows:

```
coffee -b -c proc.coffee
coffee -b example-proc.coffee
```

Now to run Agda code directly you need to have recent Agda installed
together with a recent agda-stdlib:

```
./run.sh example1
```
