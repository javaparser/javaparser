#!/usr/bin/env bash

##
## Note this script uses a custom build/fork of the Spring github-changelog-generator, based on v0.0.6 / 0.0.7-SNAPSHOT
## https://github.com/spring-io/github-changelog-generator
##
## This fork is available at https://github.com/MysterAitch/github-changelog-generator
##
## For clarity the jar is name to explicitly indicate that this is the forked version not the original.
##

#CHANGELOG_GENERATOR_JAR=./github-changelog-generator.jar
CHANGELOG_GENERATOR_JAR=./github-changelog-generator_mysteraitch.jar


echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: This script runs a preconfigured $CHANGELOG_GENERATOR_JAR"
echo "[JavaParser]: "
echo "[JavaParser]: Expected Usage: $0 MILESTONE_TITLE"
echo "[JavaParser]: Where the MILESTONE_TITLE is the title of the milestone"
echo "[JavaParser]:     e.g. $0 \"next release\""
#echo "[JavaParser]: e.g. https://github.com/javaparser/javaparser/milestone/182"


## Exit if
if [ "$#" -ne 1 ]; then
  echo "[JavaParser-ERROR]: No arguments supplied. Exiting." >&2
  echo "[JavaParser-ERROR]: Expected Usage: $0 MILESTONE_TITLE" >&2
  exit 1
fi

## Variables -- TODO: Consider making the output file configurable.
CHANGELOG_TITLE=$1
OUTPUT_FILE=temp_changelog.md

echo "[JavaParser]"
echo "[JavaParser]: - A changelog specific to that milestone will then be output to $OUTPUT_FILE"
echo "[JavaParser]: - A changelog specific to that milestone will then be output to the console"
echo "[JavaParser]"

echo "[JavaParser]: About to clear $OUTPUT_FILE ready for populating."
echo "[JavaParser]"
set -x
## Empty out the changelog:
 > $OUTPUT_FILE

## Run the changelog generator tool, to generate a changelog.
java -jar $CHANGELOG_GENERATOR_JAR --spring.config.location="release-notes-config-title.yml" "$CHANGELOG_TITLE" $OUTPUT_FILE
set +x


## Also output the generated changelog to the console.
echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: The changelog for milestone title $CHANGELOG_TITLE (also stored within $OUTPUT_FILE)"
echo "[JavaParser]"
echo ""


## Get contents of the
value=$(<$OUTPUT_FILE)
echo "$value"

