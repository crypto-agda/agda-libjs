fs   = require 'fs'
find = require 'find'
find.file /\.(agda|coffee)$/, '.', (files) ->
  fs.writeFile 'package.json', JSON.stringify
    name: "agda-libjs"
    version: "0.0.1"
    description: "JS bindings for Agda"
    main: "agda-libjs.agda"
    scripts:
      test: "echo \"Error: no test specified\" && exit 1"
    files: [
      "README.md"
      "run.sh"
    ].concat(files)
    repository:
      type: "git"
      url: "https://github.com/crypto-agda/agda-libjs"
    keywords: [
      "agda"
      "library"
    ]
    author: "Nicolas Pouillard"
    license: "BSD3"
    bugs:
      url: "https://github.com/crypto-agda/agda-libjs/issues"
    homepage: "https://github.com/crypto-agda/agda-libjs"
   #dependencies:
   #  "agda-stdlib": ">= 0.0.1"
    agda:
      include: [
        "."
        "./lib"
      ]
