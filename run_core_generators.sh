#!/usr/bin/env bash

# Runs all the code generators.
# If the node structure was changed, run_metamodel_generator.sh first!

pushd javaparser-core-generators

mvn clean package

popd

mvn clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi
