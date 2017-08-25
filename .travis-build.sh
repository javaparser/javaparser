#!/bin/bash

# Fail the whole script if any command fails
set -e

export SHELLOPTS

./.travis-build-without-test.sh

## Test
echo "running \"mvn test\" for stubparser
mvn test
