#!/bin/bash
ROOT=$TRAVIS_BUILD_DIR/..

# Fail the whole script if any command fails
set -e

export SHELLOPTS

SLUGOWNER=${TRAVIS_REPO_SLUG%/*}
if [[ "$SLUGOWNER" == "" ]]; then
  SLUGOWNER=typetools
fi

## Compile
echo "running \"mvn package\" for stubparser"
mvn package -Dmaven.test.skip=true
cp -i ./javaparser-core/target/javaparser-core-3.3.1-SNAPSHOT.jar stubparser.jar
