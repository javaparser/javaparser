#!/bin/bash

##
## This script prepares the project for release of the next version, but does so LOCALLY.
##
## Note that this script should be executed from the project's root directory (with the parent's pom.xml).
## Usage: ./scripts/release-prepare-local.sh
##

if [ "$1" = "" ]; then
  echo "[JavaParser]: "
  echo "[JavaParser]: Usage: $0 RELEASE_VERSION"
  exit 0
fi

release_version="$1"
shift


## Update poms to reflect the given release version
echo "[JavaParser]: Updating all JavaParser POM files to version: $release_version"
./scripts/pom-set-version.sh "$release_version"

## Commit these changes to git
echo "[JavaParser]: Committing all JavaParser POM files to git"
./mvnw -e scm:checkin -Dmessage="[maven] Update pom files to version $release_version"

## Add a tag for the release version
./mvnw scm:tag -Dtag="javaparser-parent-$release_version"
