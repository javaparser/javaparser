#!/usr/bin/env bash

## Exit script if any non-zero exit code (nb: some redundancy with checks below - may remove if exit code checks are thorough)
set -e
## Disallow references to non-existent environment variables
set -u
## Exit on invalid/bad pipes
set -o pipefail

#TODO --- Replace all mentions of Bintray

echo "[JavaParser]"
echo "[JavaParser]"
echo "[JavaParser]: See also: http://github.com/javaparser/javaparser/wiki/Release-Process"
echo "[JavaParser]"
echo "[JavaParser]: ##"
echo "[JavaParser]: ##"
echo "[JavaParser]: ## TODO --- Replace all mentions of Bintray"
echo "[JavaParser]: ##"
echo "[JavaParser]: ##"
echo "[JavaParser]"
echo "[JavaParser]: Before running this script, ensure that your settings.xml file (~/.m/setings.xml) has been updated with your Bintray credentials."
echo "[JavaParser]: - A template settings.xml file can be found within the dev-files directory."
echo "[JavaParser]: - You must also be added to the JavaParser organisation on Bintray for releases to be successful."
echo "[JavaParser]:"
echo "[JavaParser]: Note that the git repo uses the SSH URL to pull/push -- this, therefore, requires you to have setup SSH access to your GitHub account."
echo "[JavaParser]:"
echo "[JavaParser]: Once the release is complete and has been uploaded to Bintray, there is still an oppotunity for it to be deleted via the Bintray website."
echo "[JavaParser]: - To push it to Maven Central (therefore be available to users), it must be synchronised via the Bintray web UI."
echo "[JavaParser]: - When successful, Bintray will report 'Last Sync Status: Successfully synced and closed repo.'"
echo "[JavaParser]:"
echo "[JavaParser]: - Note that you MUST have sonatype credentials that can be entered into the Bintray web UI to trigger the sync"
echo "[JavaParser]:   (the same credentials used to login to http://oss.sonatype.org/ )."
echo "[JavaParser]:"
echo "[JavaParser]: - Note that you MUST have your sonatype account linked to the JavaParser coordinates, to trigger the sync FROM Bintray TO Sonatype/Maven Central."
echo "[JavaParser]:   This can be done by having an existing committer open a ticket at https://issues.sonatype.org/ ."
echo "[JavaParser]"
echo "[JavaParser]"

set -x

./mvnw --errors --show-version \
  -Darguments="-DskipTests" release:perform

if [ "$?" -ne 0 ]; then
  echo "Error when performing release:perform"
  exit 10;
fi

set +x
