#!/usr/bin/env bash

##
## Note this script uses a custom build/fork of the Spring github-changelog-generator, based on v0.0.6 / 0.0.7-SNAPSHOT
## https://github.com/spring-io/github-changelog-generator
##
## This fork is available at https://github.com/MysterAitch/github-changelog-generator
##
## For clarity, the jar is named to explicitly indicate that this is the forked version not the original.
##


## Exit if number of given parameters is incorrect (expecting 1 - the milestone id)
if [ "$#" -ne 1 ]; then
  echo "[JavaParser-ERROR]: No arguments supplied. Exiting." >&2
  echo "[JavaParser-ERROR]: Expected Usage: $0 MILESTONE_ID" >&2
  exit 3
fi

## Variables
CHANGELOG_ID=$1

#CHANGELOG_GENERATOR_JAR=./github-changelog-generator.jar
CHANGELOG_GENERATOR_JAR=./github-changelog-generator_mysteraitch.jar
CONFIG_FILE_LOCATION="release-notes-config-id.yml"
OUTPUT_FILE=temp_changelog.md ## TODO: Consider making the output file configurable.


echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: This script runs a preconfigured $CHANGELOG_GENERATOR_JAR"
echo "[JavaParser]: "
echo "[JavaParser]: Expected Usage: $0 MILESTONE_ID"
echo "[JavaParser]: Where the MILESTONE_ID is the number within the milestone URL"
echo "[JavaParser]:     e.g. $0 182"
#echo "[JavaParser]: e.g. https://github.com/javaparser/javaparser/milestone/182"
echo "[JavaParser]"
echo "[JavaParser]: - A changelog specific to that milestone will then be output to $OUTPUT_FILE"
echo "[JavaParser]: - A changelog specific to that milestone will then be output to the console"
echo "[JavaParser]"

echo "[JavaParser]: About to clear $OUTPUT_FILE ready for populating."
echo "[JavaParser]"
set -x
## Empty out the changelog:
 # shellcheck disable=SC2188
 > $OUTPUT_FILE

## Run the changelog generator tool, to generate a changelog.
java -jar $CHANGELOG_GENERATOR_JAR --spring.config.location="$CONFIG_FILE_LOCATION" "$CHANGELOG_ID" $OUTPUT_FILE
CHANGELOG_GENERATOR_EXIT_CODE=$?
set +x

## If the generator failed (e.g. due to an invalid milestone reference), exit this script.
if [ $CHANGELOG_GENERATOR_EXIT_CODE -ne 0 ]; then
  echo "[JavaParser-ERROR]: Generation of the changelog failed. Exiting." >&2
  exit 4
fi


## Also display the generated changelog to the console.
CHANGELOG_CONTENTS=$(<$OUTPUT_FILE)

echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: The changelog for milestone ID $CHANGELOG_ID (also stored within $OUTPUT_FILE)"
echo "[JavaParser]"
echo ""
echo "$CHANGELOG_CONTENTS"
