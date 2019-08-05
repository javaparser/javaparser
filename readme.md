# JavaParser

[![Maven Central](https://img.shields.io/maven-central/v/com.github.javaparser/javaparser-core.svg)](http://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22com.github.javaparser%22%20AND%20a%3A%22javaparser-core%22)
[![Build Status](https://travis-ci.org/javaparser/javaparser.svg?branch=master)](https://travis-ci.org/javaparser/javaparser)
[![Coverage Status](https://coveralls.io/repos/javaparser/javaparser/badge.svg?branch=master&service=github)](https://coveralls.io/github/javaparser/javaparser?branch=master)
[![Join the chat at https://gitter.im/javaparser/javaparser](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/javaparser/javaparser?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![License LGPL-3/Apache-2.0](https://img.shields.io/badge/license-LGPL--3%2FApache--2.0-blue.svg)](LICENSE)

This project contains a set of libraries implementing a Java 1.0 - Java 12 Parser with advanced analysis functionalities.

Our main site is at [JavaParser.org](http://javaparser.org)

## Setup

The project binaries are available in Maven Central. 

We strongly advise users to adopt Maven, Gradle or another build system for their projects.
If you are not familiar with them we suggest taking a look at the maven quickstart projects 
([javaparser-maven-sample](https://github.com/javaparser/javaparser-maven-sample), 
[javasymbolsolver-maven-sample](https://github.com/javaparser/javasymbolsolver-maven-sample)).

Just add the following to your maven configuration or tailor to your own dependency management system.

[Please refer to the Migration Guide when upgrading from 2.5.1 to 3.0.0+](https://github.com/javaparser/javaparser/wiki/Migration-Guide)

**Maven**: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-symbol-solver-core</artifactId>
    <version>3.14.9</version>
</dependency>
```

**Gradle**:

```
implementation 'com.github.javaparser:javaparser-symbol-solver-core:3.14.9'
```

Since Version 3.5.10, the JavaParser project includes the JavaSymbolSolver. 
While JavaParser generates an Abstract Syntax Tree, JavaSymbolSolver analyzes that AST and is able to find 
the relation between an element and its declaration (e.g. for a variable name it could be a parameter of a method, providing information about its type, position in the AST, ect).

Using the dependency above will add both JavaParser and JavaSymbolSolver to your project. If you only need the core functionality of parsing Java source code in order to traverse and manipulate the generated AST, you can reduce your projects boilerplate by only including JavaParser to your project:

**Maven**: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core</artifactId>
    <version>3.14.9</version>
</dependency>
```

**Gradle**:

```
implementation 'com.github.javaparser:javaparser-core:3.14.9'
```

Since version 3.6.17 the AST can be serialized to JSON.
There is a separate module for this:

**Maven**: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core-serialization</artifactId>
    <version>3.14.9</version>
</dependency>
```

**Gradle**:

```
implementation 'com.github.javaparser:javaparser-core-serialization:3.14.9'
```

## How To Compile Sources

If you checked out the project from GitHub you can build the project with maven using:

```
mvn clean install
```

If you checkout the sources and want to view the project in an IDE, it is best to first generate some of the source files; otherwise you will get many compilation complaints in the IDE. (mvn clean install already does this for you.)

```
mvn javacc:javacc
```

If you modify the code of the AST nodes, specifically if you add or remove fields or node classes,
the code generators will update a lot of code for you.
The `run_metamodel_generator.sh` script will rebuild the metamodel,
which is used by the code generators which are run by `run_core_generators.sh`
Make sure that `javaparser-core` at least compiles before you run these.

## More information

#### [JavaParser.org](https://javaparser.org) is the main information site.

## License

JavaParser is available either under the terms of the LGPL License or the Apache License. You as the user are entitled to choose the terms under which adopt JavaParser.

For details about the LGPL License please refer to [LICENSE.LGPL](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.LGPL).

For details about the Apache License please refer to [LICENSE.APACHE](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.APACHE).
