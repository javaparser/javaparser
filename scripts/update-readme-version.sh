#!/bin/bash

##
## Note that this script should be executed from the project's root directory (with the parent's pom.xml).
## Usage: ./scripts/update-readme-version.sh
##


echo "[JavaParser]: Updating JavaParser versions within readme.md to reflect the current version."

## Note: Do not need to update child modules, therefore can run maven non-recursively.
./mvnw -e -non-recursive compile -Pupdate-readme
