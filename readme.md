## Stub Parser

This package contains a parser for the Checker Framework's stub files:
https://checkerframework.org/manual/#stub
It is a fork of the [JavaParser](http://javaparser.org) project.

## Differences between the StubParser and JavaParser

Following list is the differences that were added to the JavaParser to adjust it for using as StubParser for 
[the Checker Framework](https://github.com/typetools/checker-framework).

1. StubUnit class that represents the parsed [stubfile](https://checkerframework.org/manual/#stub).
2. Changes at the java.jj file to parse the stub files.
3. Methods for parsing the stub files at the JavaParser.class.

To check the code difference "git diff" could be used. 
[Stackoverflow link on how to get diff between forks](https://stackoverflow.com/questions/4927519/diff-a-git-fork).
Enter the root directory of the StubParser and perform following commands:
```bash
git remote add original https://github.com/javaparser/javaparser
git fetch original
git diff HEAD original/master
```

## Updating from upstream JavaParser

This section describes how to incorporate changes from JavaParser into
StubParser.  Only developers, not users, of StubParser need to do this.

1. Fork [the StubParser project](https://github.com/typetools/stubparser) to your GitHub account.
2. Enable Travis build for your fork of the StubParser. 
[How to get started with Travis CI](https://docs.travis-ci.com/user/getting-started/#To-get-started-with-Travis-CI).
3. Clone the repository.
```bash
git clone https://github.com/{user.name}/stubparser
```
4. Enter the main directory of the local project.
```bash
cd stubparser
```
5. Create and checkout a branch named `updating`.
```bash
git checkout -b updating
```
6. Pull the upstream of [the JavaParser project](https://github.com/javaparser/javaparser).
```bash
git pull https://github.com/javaparser/javaparser master
```
7. Resolve conflicts if required and commit it.
8. Run maven tests in the root StubParser directory. If any tests fail, fix them before continuing.
```bash
mvn test
```
9. Push commits to your fork of the StubParser.
```bash
git push
```
10. Check that the Travis build was successful. If not, resolve the issues and repeat steps 7-9.
11. Create a pull request to the typetools/stubparser.

## Original JavaParser README

The remainder of this README file is the original JavaParser README.

## Java Parser and Abstract Syntax Tree

This package contains a Java 1.0 - Java 9 Parser with AST generation and visitor support.

Our main site is at [JavaParser.org](http://javaparser.org)

[![Maven Central](https://img.shields.io/maven-central/v/com.github.javaparser/javaparser-core.svg)](http://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22com.github.javaparser%22%20AND%20a%3A%22javaparser-core%22)
[![Build Status](https://travis-ci.org/javaparser/javaparser.svg?branch=master)](https://travis-ci.org/javaparser/javaparser)
[![Coverage Status](https://coveralls.io/repos/javaparser/javaparser/badge.svg?branch=master&service=github)](https://coveralls.io/github/javaparser/javaparser?branch=master)
[![Join the chat at https://gitter.im/javaparser/javaparser](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/javaparser/javaparser?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

## Dependency Management

The project binaries are available in Maven Central.  Just add the following to your maven configuration or tailor to your own dependency management system.

[Please refer to the Migration Guide when upgrading from 2.5.1 to 3.0.0+](https://github.com/javaparser/javaparser/wiki/Migration-Guide)

**Maven**: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-symbol-solver-core</artifactId>
    <version>3.5.14</version>
</dependency>
```

**Gradle**:

```
compile 'com.github.javaparser:javaparser-symbol-solver-core:3.5.14'
```



Since Version 3.5.10, the JavaParser project includes the JavaSymbolSolver. While JavaParser generates an Abstract Syntax Tree, JavaSymbolSolver analyzes that AST and is able to find the relation between an element and its declaration (e.g. for a variable name it could be a parameter of a method, providing information about its type, position in the AST, ect).

Using the dependency above will add both JavaParser and JavaSymbolSolver to your project. If you only need the core functionality of parsing Java source code in order to traverse and manipulate the generated AST, you can reduce your projects boilerplate by only including JavaParser to your project:

**Maven**: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core</artifactId>
    <version>3.5.14</version>
</dependency>
```

**Gradle**:

```
compile 'com.github.javaparser:javaparser-core:3.5.14'
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

#### [JavaParser.org](https://www.javaparser.org) is the main information site.

## License

JavaParser is available either under the terms of the LGPL License or the Apache License. You as the user are entitled to choose the terms under which adopt JavaParser.

For details about the LGPL License please refer to [LICENSE.LGPL](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.LGPL).

For details about the Apache License please refer to [LICENSE.APACHE](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.APACHE).
