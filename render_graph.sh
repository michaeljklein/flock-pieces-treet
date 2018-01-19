#!/bin/bash

set -ex

rm -f dependency_graph.dot dependency_graph.jpg

# https://github.com/yav/graphmod
# stack install graphmod
find src -name '*.hs' | xargs graphmod -q > dependency_graph.dot

# brew install graphviz
dot -Tjpg dependency_graph.dot -o dependency_graph.jpg

