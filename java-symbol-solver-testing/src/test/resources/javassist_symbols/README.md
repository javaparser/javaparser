For the tests regarding resolving symbols in Jar files, we need some jar files. Some other tests within JavaSymbolSolver use established external jars for that purpose. Given the very specific cases we need here, that would severly complicate writing and maintaining tests. Therefore, I've decided to write custom jars for the cases we need.

`main_jar` contains most of the necessary classes, `included_jar` and `excluded_jar` both contain an interface and a superclass. Included_jar is included in the combined type solver, while excluded_jar is not.

If you need to make changes to either jar, run the following commands to generate the new jars (assuming that a JDK bin directory is in your path).
When you need to rebuild the jar, it is important to make sure you actually update the jar in git. Jar-files are in the git-ignore, so you'll have to force-add them using `git -f main_jar.jar`.

## Excluded jar

```
In ./java-symbol-solver-testing/src/test/resources/javassist_symbols/excluded_jar
javac -d result/ src/com/github/javaparser/javasymbolsolver/javassist_symbols/excluded_jar/*.java
cd result/
jar cf ../excluded_jar.jar com/*
```

## Included jar

```
In ./java-symbol-solver-testing/src/test/resources/javassist_symbols/included_jar
javac -d result/ src/com/github/javaparser/javasymbolsolver/javassist_symbols/included_jar/*.java
cd result/
jar cf ../included_jar.jar com/*
```

## Main jar

```
In ./java-symbol-solver-testing/src/test/resources/javassist_symbols/main_jar
javac -cp ../included_jar/included_jar.jar;../excluded_jar/excluded_jar.jar -d result/ src/com/github/javaparser/javasymbolsolver/javassist_symbols/main_jar/*.java
cd result/
jar cf ../main_jar.jar com/*
```

(`result` was chosen as a name instead of `target` or `out`, because those seem to be ignored.)