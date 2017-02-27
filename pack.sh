VERSION=`./gradlew version | grep Version | cut -f 2 -d " "`
PASSPHRASE=`cat ~/.gnupg/passphrase.txt`
GPGPARAMS="--passphrase $PASSPHRASE --batch --yes --no-tty"
./gradlew assemble generatePom

echo
echo CORE
echo

mv java-symbol-solver-core/build/libs/java-symbol-solver-core.jar java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}.jar
mv java-symbol-solver-core/build/libs/java-symbol-solver-core-javadoc.jar java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}-javadoc.jar
mv java-symbol-solver-core/build/libs/java-symbol-solver-core-sources.jar java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}-sources.jar
sed s/unspecified/$VERSION/g java-symbol-solver-core/build/pom.xml > java-symbol-solver-core/build/pom_corrected.xml
mv java-symbol-solver-core/build/pom_corrected.xml java-symbol-solver-core/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-core/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}.jar
gpg $GPGPARAMS -ab java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}-javadoc.jar
gpg $GPGPARAMS -ab java-symbol-solver-core/build/libs/java-symbol-solver-core-${VERSION}-sources.jar
cd java-symbol-solver-core/build/libs
jar -cvf bundle-java-symbol-solver-core.jar ../pom.xml ../pom.xml.asc java-symbol-solver-core-${VERSION}.jar java-symbol-solver-core-${VERSION}.jar.asc java-symbol-solver-core-${VERSION}-javadoc.jar java-symbol-solver-core-${VERSION}-javadoc.jar.asc java-symbol-solver-core-${VERSION}-sources.jar java-symbol-solver-core-${VERSION}-sources.jar.asc
cd ../../..

echo
echo MODEL
echo

mv java-symbol-solver-model/build/libs/java-symbol-solver-model.jar java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}.jar
mv java-symbol-solver-model/build/libs/java-symbol-solver-model-javadoc.jar java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}-javadoc.jar
mv java-symbol-solver-model/build/libs/java-symbol-solver-model-sources.jar java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}-sources.jar
sed s/unspecified/$VERSION/g java-symbol-solver-model/build/pom.xml > java-symbol-solver-model/build/pom_corrected.xml
mv java-symbol-solver-model/build/pom_corrected.xml java-symbol-solver-model/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-model/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}.jar
gpg $GPGPARAMS -ab java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}-javadoc.jar
gpg $GPGPARAMS -ab java-symbol-solver-model/build/libs/java-symbol-solver-model-${VERSION}-sources.jar
cd java-symbol-solver-model/build/libs
jar -cvf bundle-java-symbol-solver-model.jar ../pom.xml ../pom.xml.asc java-symbol-solver-model-${VERSION}.jar java-symbol-solver-model-${VERSION}.jar.asc java-symbol-solver-model-${VERSION}-javadoc.jar java-symbol-solver-model-${VERSION}-javadoc.jar.asc java-symbol-solver-model-${VERSION}-sources.jar java-symbol-solver-model-${VERSION}-sources.jar.asc
cd ../../..

echo
echo LOGIC
echo

mv java-symbol-solver-logic/build/libs/java-symbol-solver-logic.jar java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}.jar
mv java-symbol-solver-logic/build/libs/java-symbol-solver-logic-javadoc.jar java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}-javadoc.jar
mv java-symbol-solver-logic/build/libs/java-symbol-solver-logic-sources.jar java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}-sources.jar
sed s/unspecified/$VERSION/g java-symbol-solver-logic/build/pom.xml > java-symbol-solver-logic/build/pom_corrected.xml
mv java-symbol-solver-logic/build/pom_corrected.xml java-symbol-solver-logic/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-logic/build/pom.xml
gpg $GPGPARAMS -ab java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}.jar
gpg $GPGPARAMS -ab java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}-javadoc.jar
gpg $GPGPARAMS -ab java-symbol-solver-logic/build/libs/java-symbol-solver-logic-${VERSION}-sources.jar
cd java-symbol-solver-logic/build/libs
jar -cvf bundle-java-symbol-solver-logic.jar ../pom.xml ../pom.xml.asc java-symbol-solver-logic-${VERSION}.jar java-symbol-solver-logic-${VERSION}.jar.asc java-symbol-solver-logic-${VERSION}-javadoc.jar java-symbol-solver-logic-${VERSION}-javadoc.jar.asc java-symbol-solver-logic-${VERSION}-sources.jar java-symbol-solver-logic-${VERSION}-sources.jar.asc
cd ../../..

mkdir -p release
mv java-symbol-solver-core/build/libs/bundle-java-symbol-solver-core.jar release
mv java-symbol-solver-model/build/libs/bundle-java-symbol-solver-model.jar release
mv java-symbol-solver-logic/build/libs/bundle-java-symbol-solver-logic.jar release