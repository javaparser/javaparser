* mvn install

* mvn javadoc:jar

* mvn source:jar

gpg -ab java-symbol-solver-model/pom.xml
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.2.jar
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.2-javadoc.jar
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.2-sources.jar

mkdir build
cd build
cp ../java-symbol-solver-model/pom.xml .
cp ../java-symbol-solver-model/pom.xml.asc .
cp ../java-symbol-solver-model/target/*.jar .
cp ../java-symbol-solver-model/target/*.asc .
jar -cvf bundle-java-symbol-solver-model.jar pom.xml pom.xml.asc java-symbol-solver-model-0.2.jar java-symbol-solver-model-0.2.jar.asc java-symbol-solver-model-0.2-javadoc.jar java-symbol-solver-model-0.2-javadoc.jar.asc java-symbol-solver-model-0.2-sources.jar java-symbol-solver-model-0.2-sources.jar.asc