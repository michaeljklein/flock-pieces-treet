#!/bin/bash

set -ex

rm -f graph.dot graph.jpg

# https://github.com/yav/graphmod
find src -name '*.hs' | xargs graphmod -q > graph.dot

# brew install graphviz
# brew info graphviz
/usr/local/Cellar/graphviz/2.40.1/bin/dot -Tjpg graph.dot -o graph.jpg

