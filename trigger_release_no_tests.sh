#!/usr/bin/env bash

mvn -e --batch-mode -Darguments="-DskipTests" release:clean release:prepare release:perform
