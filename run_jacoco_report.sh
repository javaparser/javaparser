#!/usr/bin/env bash

# Run the tests
./mvnw --errors --show-version  clean test

# Run the jacoco report
./mvnw --errors --show-version  -Pjacoco.report validate

echo "Open the index.html file in the javaparser-jacoco-report/target/jacoco-reports directory to view the report."
echo "If you want to process the report find the jacoco.xml file in the same directory."