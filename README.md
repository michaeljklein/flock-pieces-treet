# flock-pieces-treet

`TreeT` is a recursive and monad transformer with interesting properties, not unlike free monads (`free: Control.Monad.Free`).


## Module Dependency Graph

```bash
render_graph.sh
```

![dependency_graph.jpg](https://github.com/michaeljklein/flock-pieces-treet/raw/master/dependency_graph.jpg "graphmod dependency graph; see dependency_graph.dot, render_graph.sh")


## Tree

```bash
> git rev-parse HEAD
19f61261fd28b1d1740f390565a866df8002ace8

> tree .
.
├── LICENSE
├── README.md
├── Setup.hs
├── app
│   └── Main.hs
├── bench
│   └── Bench.hs
├── build_docs.rb
├── dependency_graph.dot
├── dependency_graph.jpg
├── doc
│   └── html
│       └── flock-pieces-treet
│           ├── Control-Arrow-Tree.html
│           ├── Control-Monad-Trans-TreeT.html
│           ├── Data-Bidistributable.html
│           ├── Data-Rope.html
│           ├── Data-SwapList.html
│           ├── doc-index.html
│           ├── flock-pieces-treet.haddock
│           ├── flock-pieces-treet.txt
│           ├── haddock-util.js
│           ├── hslogo-16.png
│           ├── index.html
│           ├── minus.gif
│           ├── ocean.css
│           ├── plus.gif
│           ├── src
│           │   ├── Control.Arrow.Tree.html
│           │   ├── Control.Monad.Trans.TreeT.html
│           │   ├── Data.Bidistributable.html
│           │   ├── Data.Rope.html
│           │   ├── Data.SwapList.html
│           │   ├── highlight.js
│           │   └── style.css
│           └── synopsis.png
├── flock-pieces-treet.cabal
├── render_graph.sh
├── src
│   ├── Control
│   │   ├── Arrow
│   │   │   └── Tree.hs
│   │   └── Monad
│   │       └── Trans
│   │           └── TreeT.hs
│   └── Data
│       ├── Bidistributable.hs
│       ├── Rope.hs
│       └── SwapList.hs
├── stack.yaml
└── test
    └── Test.hs

13 directories, 39 files
```


