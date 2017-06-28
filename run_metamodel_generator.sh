#!/usr/bin/env bash

# Rebuilds the metamodel based on the nodes in javaparser-core

mvn clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi

pushd javaparser-metamodel-generator

mvn clean package

popd

mvn clean install -DskipTests
if [ "$?" -ne 0 ]; then
    exit 1
fi
