#!/bin/bash

set -ex

echo 'Generating tags file.'

# Install hasktags with: stack install hasktags
# https://github.com/MarcWeber/hasktags
git ls-files | grep -v '^doc/' | xargs hasktags

echo 'Running unused:'
# Install unused with: stack install unused
# https://github.com/joshuaclayton/unused
unused | tee unused.txt

