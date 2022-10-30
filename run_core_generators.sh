#!/usr/bin/env bash

# Runs all the code generators.
# If the node structure was changed, run_metamodel_generator.sh first!

# Remember current directory
pushd javaparser-core-generators

# Generate code
../mvnw --errors --show-version -B clean package -P run-generators -DskipTests

# Go back to previous directory
popd

# Fresh code has been generated in core, so rebuild the whole thing again.
./mvnw --errors --show-version -B clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi
