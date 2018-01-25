#!/bin/bash

set -ex

echo 'Generating tags file'
git ls-files | xargs ctags

echo 'Running unused:'
echo '(https://github.com/joshuaclayton/unused)'
unused

