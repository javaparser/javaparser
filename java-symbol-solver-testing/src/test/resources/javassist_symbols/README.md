For the tests regarding resolving symbols in Jar files, we need some jar files. Some other tests within JavaSymbolSolver use established external jars for that purpose. Given the very specific cases we need here, that would severly complicate writing and maintaining tests. Therefore, I've decided to write custom jars for the cases we need.

`main_jar` contains most of the necessary classes, while `extra_jar` (TODO) is used for main_jar to refer to with the goal that it would not be included in the SymbolSolver and thus trigger an error.

If you need to make changes to either jar, run the following commands to generate the new jars (assuming that a JDK bin directory is in your path).

## Main jar

```
In ./java-symbol-solver-testing/src/test/resources/javassist_symbols/main_jar
javac -d result/ src/com/github/javaparser/javasymbolsolver/javassist_symbols/main_jar/ConcreteClass.java
cd result/
jar cf ../main_jar.jar com/*
```

(`result` was chosen as a name instead of `target` or `out`, because those seem to be ignored.)