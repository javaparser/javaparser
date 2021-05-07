#!/bin/bash

##
## Loosely based on scripts at: https://gist.github.com/swthomas55/8efd7fe8317b447f58f7
##
## Note that this script should be executed from the project's root directory (with the parent's pom.xml).
## Usage: ./scripts/pom-set-version.sh
##
## Requires: Maven versions plugin
##

if [ "$1" = "" ]; then
  echo "[JavaParser]: Sets the version number of the specified POM files or the pom.xml in the specified directories to VERSION"
  echo "[JavaParser]: Usage: $0 VERSION"
  exit 0
fi

version="$1"
shift

echo "[JavaParser]: Updating all JavaParser POM files to version: $version"

./mvnw -e versions:set -DnewVersion="$version"
