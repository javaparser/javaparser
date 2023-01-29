# jmlparser -- A Parser for Java and Java Modeling Language

[![Build and test (using maven)](https://github.com/wadoon/jmlparser/actions/workflows/maven_tests.yml/badge.svg?branch=master)](https://github.com/wadoon/jmlparser/actions/workflows/maven_tests.yml)
[![License LGPL-3](https://img.shields.io/badge/license-LGPL--3-blue.svg)](LICENSE)

This project provides a library for Java and [Java Modeling Language
(JML)](https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman.html). JML is a
formal specification language for Java which is used by verification
([OpenJML](https://openjml.org/), [KeY](https://key-project.org)) and test tools
([JMLUnitNG](https://github.com/FreeAndFair/JMLUnitNG)).

**Features** The library provides features:

* Parsing of Java files (incl. 17) including JML specification
* Providing a (mutable) unified abstract syntax tree (AST) for Java and JML
* Name resolution for JML
* Common code transformation for JML
* Validation checks

This project builds upon the [JavaParser project](http://javaparser.org).

## Setup

The project binaries are available via Github Packages. Note, that Github
Packages currently requires an authenthication.

**Gradle**:

```
repositories {
    maven {
        url = uri("https://maven.pkg.github.com/wadoon/jmlparser")
        credentials {
            username = project.findProperty("gpr.user") as String? ?: System.getenv("USERNAME")
            password = project.findProperty("gpr.key") as String? ?: System.getenv("TOKEN")
        }
    }
}

dependencies{ ... 
  implementation("io.github.wadoon:jmlparser-symbol-solver-core:3.24.3-SNAPSHOT")
}
```

## How To Compile Sources

If you checked out the project's source code from GitHub, you can build the project with maven using:

```
./mvnw clean install
```

If you want to generate the packaged jar files from the source files, you run the following maven command:

```
mvnw package
```

**NOTE** the jar files for the two modules can be found in:

- `javaparser-core/target/javaparser-core-\<version\>.jar`
- `javaparser-symbol-solver-core/target/javaparser-symbol-solver-core-\<version\>.jar`

If you checkout the sources and want to view the project in an IDE, it is best
to first generate some of the source files; otherwise you will get many
compilation complaints in the IDE. (`mvnw clean install` already does this for
you.)

```
mvnw javacc:javacc
```

If you modify the code of the AST nodes, specifically if you add or remove
fields or node classes, the code generators will update a lot of code for you.
The `run_metamodel_generator.sh` script will rebuild the metamodel, which is
used by the code generators which are run by `run_core_generators.sh` Make sure
that `javaparser-core` at least compiles before you run these.

**Note**: for Eclipse IDE follow the steps described in the wiki:
https://github.com/javaparser/javaparser/wiki/Eclipse-Project-Setup-Guide

## License

jmlparser is available either under the terms of the LGPL License or the Apache
License. You as the user are entitled to choose the terms under which adopt
JavaParser.

For details about the LGPL License please refer
to [LICENSE.LGPL](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.LGPL).
