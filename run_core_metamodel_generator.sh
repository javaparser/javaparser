#!/usr/bin/env bash

# Rebuilds the metamodel based on the nodes in javaparser-core

# We introspect the nodes in javaparser-core, so we need an update build of it. 
./mvnw --errors --show-version -B clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi

# Remember current directory
pushd javaparser-core-metamodel-generator

# Generate code
../mvnw --errors --show-version -B clean package -P run-generators -DskipTests

# Go back to previous directory
popd

# Fresh code has been generated in core, so rebuild the whole thing again.
./mvnw --errors --show-version -B clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi
