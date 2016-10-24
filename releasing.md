After fighting with different plugins for automatically deploy new versions to Maven central
we currently use a manual process. As primitive as it is it actually works.

First we generate all thejars we need to generate:

* mvn install
* mvn javadoc:jar
* mvn source:jar

For each module we sign the pom and all the jars:

```
gpg -ab java-symbol-solver-model/pom.xml
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.3.2.jar
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.3.2-javadoc.jar
gpg -ab java-symbol-solver-model/target/java-symbol-solver-model-0.3.2-sources.jar


gpg -ab java-symbol-solver-logic/pom.xml
gpg -ab java-symbol-solver-logic/target/java-symbol-solver-logic-0.3.2.jar
gpg -ab java-symbol-solver-logic/target/java-symbol-solver-logic-0.3.2-javadoc.jar
gpg -ab java-symbol-solver-logic/target/java-symbol-solver-logic-0.3.2-sources.jar

gpg -ab java-symbol-solver-core/pom.xml
gpg -ab java-symbol-solver-core/target/java-symbol-solver-core-0.3.2.jar
gpg -ab java-symbol-solver-core/target/java-symbol-solver-core-0.3.2-javadoc.jar
gpg -ab java-symbol-solver-core/target/java-symbol-solver-core-0.3.2-sources.jar

gpg -ab java-symbol-solver-examples/pom.xml
gpg -ab java-symbol-solver-examples/target/java-symbol-solver-examples-0.3.2.jar
gpg -ab java-symbol-solver-examples/target/java-symbol-solver-examples-0.3.2-javadoc.jar
gpg -ab java-symbol-solver-examples/target/java-symbol-solver-examples-0.3.2-sources.jar
```

We then package everything in a bundle:

```
mkdir build
cd build
cp ../java-symbol-solver-model/pom.xml .
cp ../java-symbol-solver-model/pom.xml.asc .
cp ../java-symbol-solver-model/target/*.jar .
cp ../java-symbol-solver-model/target/*.asc .
jar -cvf bundle-java-symbol-solver-model.jar pom.xml pom.xml.asc java-symbol-solver-model-0.3.2.jar java-symbol-solver-model-0.3.2.jar.asc java-symbol-solver-model-0.3.2-javadoc.jar java-symbol-solver-model-0.3.2-javadoc.jar.asc java-symbol-solver-model-0.3.2-sources.jar java-symbol-solver-model-0.3.2-sources.jar.asc

cp ../java-symbol-solver-logic/pom.xml .
cp ../java-symbol-solver-logic/pom.xml.asc .
cp ../java-symbol-solver-logic/target/*.jar .
cp ../java-symbol-solver-logic/target/*.asc .
jar -cvf bundle-java-symbol-solver-logic.jar pom.xml pom.xml.asc java-symbol-solver-logic-0.3.2.jar java-symbol-solver-logic-0.3.2.jar.asc java-symbol-solver-logic-0.3.2-javadoc.jar java-symbol-solver-logic-0.3.2-javadoc.jar.asc java-symbol-solver-logic-0.3.2-sources.jar java-symbol-solver-logic-0.3.2-sources.jar.asc

cp ../java-symbol-solver-core/pom.xml .
cp ../java-symbol-solver-core/pom.xml.asc .
cp ../java-symbol-solver-core/target/*.jar .
cp ../java-symbol-solver-core/target/*.asc .
jar -cvf bundle-java-symbol-solver-core.jar pom.xml pom.xml.asc java-symbol-solver-core-0.3.2.jar java-symbol-solver-core-0.3.2.jar.asc java-symbol-solver-core-0.3.2-javadoc.jar java-symbol-solver-core-0.3.2-javadoc.jar.asc java-symbol-solver-core-0.3.2-sources.jar java-symbol-solver-core-0.3.2-sources.jar.asc

cp ../java-symbol-solver-examples/pom.xml .
cp ../java-symbol-solver-examples/pom.xml.asc .
cp ../java-symbol-solver-examples/target/*.jar .
cp ../java-symbol-solver-examples/target/*.asc .
jar -cvf bundle-java-symbol-solver-examples.jar pom.xml pom.xml.asc java-symbol-solver-examples-0.3.2.jar java-symbol-solver-examples-0.3.2.jar.asc java-symbol-solver-examples-0.3.2-javadoc.jar java-symbol-solver-examples-0.3.2-javadoc.jar.asc java-symbol-solver-examples-0.3.2-sources.jar java-symbol-solver-examples-0.3.2-sources.jar.asc
```

Then we sign the parent pom.xml and we zip the parent.pom together with its signature:

```
gpg -ab pom.xml
jar -cvf bundle-java-symbol-solver-parent.jar pom.xml pom.xml.asc
```

We upload all the bundle jars to sonatype and then release them.