#!/usr/bin/env bash

mvn -e --batch-mode release:clean release:prepare release:perform
