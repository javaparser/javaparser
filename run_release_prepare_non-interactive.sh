#!/usr/bin/env bash

## Exit script if any non-zero exit code (nb: some redundancy with checks below - may remove if exit code checks are thorough)
set -e
## Disallow references to non-existent environment variables
set -u
## Exit on invalid/bad pipes
set -o pipefail


echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: See also: http://github.com/javaparser/javaparser/wiki/Release-Process"
echo "[JavaParser]:"
echo "[JavaParser]: This script pulls the latest code from your default tracking branch (set automatically when using git clone)."
echo "[JavaParser]: This script then performs the maven release:prepare."
echo "[JavaParser]: - Note that release:prepare requires user input to define the new and next version."
echo "[JavaParser]:"
echo "[JavaParser]: Once the release has been prepared, several commits will have been created locally but not pushed (configured within pom.xml)."
echo "[JavaParser]: These locally created commits (AND THE NEW TAG!) must then be manually pushed."
echo "[JavaParser]:"
echo "[JavaParser]: - The release prepare can undone either via release:revert -- but note that this will create new revert commits."
echo "[JavaParser]:"
echo "[JavaParser]: - Alternatively, it can be undone by manually deleting the tag and resetting the current branch's head."
echo "[JavaParser]:   (e.g. git reset --hard HEAD^3 to go back three commits, or git reset --hard <SHA>)."
echo "[JavaParser]:   You may also need to manually delete pom backup files."
echo "[JavaParser]:"
echo "[JavaParser]: - As a last resort, you can delete your local copy and clone the repo again."
echo "[JavaParser]"
echo "[JavaParser]"


## TODO: Consider the ability to pass toggles for running tests (or not)
## TODO: Consider the ability to pass toggles for doing a dry-run (or not)
if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <release-version> <new-development-version>" >&2
  echo "Example: $0 3.24.0 3.24.1-SNAPSHOT" >&2
  exit 1
fi

## Pass arguments into readable variable names
release_version=$1
next_development_snapshot_version=$2

## Use a standard version for the git tag of each release:
git_tag="javaparser-parent-${release_version}"


echo "[JavaParser]"
echo "[JavaParser] ================================================================"
echo "[JavaParser]: PREPARING RELEASE"
echo "[JavaParser]:            Release Version: ${release_version}"
echo "[JavaParser]:            Release Git Tag: ${git_tag}"
echo "[JavaParser]:      Next Snapshot Version: ${next_development_snapshot_version} "
echo "[JavaParser] ================================================================"
echo "[JavaParser]"



set -x


## Start the release from a clean start
./mvnw --errors --show-version clean

if [ "$?" -ne 0 ]; then
  echo "Error when performing clean"
  exit 102
fi


## Do a non-interactive release, using values passed as script arguments
## Note: The flag `-Darguments` is used to pass arguments to submodules
./mvnw --errors --show-version --batch-mode \
  -Darguments="-DskipTests" release:prepare \
    -Dtag="${git_tag}" \
    -DreleaseVersion="${release_version}" \
    -DdevelopmentVersion="${next_development_snapshot_version}"

if [ "$?" -ne 0 ]; then
  echo "Error when performing release:prepare"
  exit 103
fi


set +x

echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: Assuming the release:prepare is successful, you MUST now push the changes."
echo "[JavaParser]: - Specifically, release:perform requires the newly created tag to have been pushed."
echo "[JavaParser]"
echo "[JavaParser]: This can be achieved using: \`git push --follow-tags\`."
echo "[JavaParser]: Follow tags will push any tags associated with the current head commit."
echo "[JavaParser]: Alternatively, you can push the tag itself using \`git push <repo-name> <tag-name>\`."
echo "[JavaParser]"
echo "[JavaParser]"
