## Java Parser and Abstract Syntax Tree

This package contains a Java 1.0 - Java 9 Parser with AST generation and visitor support.

The AST records the source code structure.
You can analyze source code for any purpose.
It is possible to change the AST nodes or create new ones to modify the source code.

When you need not only the text from the source code but you also need type information,
you can use [the Java Symbol Solver project.](https://github.com/javaparser/javasymbolsolver)

[![Maven Central](https://img.shields.io/maven-central/v/com.github.javaparser/javaparser-core.svg)](http://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22com.github.javaparser%22%20AND%20a%3A%22javaparser-core%22)
[![Build Status](https://travis-ci.org/javaparser/javaparser.svg?branch=master)](https://travis-ci.org/javaparser/javaparser)
[![Coverage Status](https://coveralls.io/repos/javaparser/javaparser/badge.svg?branch=master&service=github)](https://coveralls.io/github/javaparser/javaparser?branch=master)
[![Join the chat at https://gitter.im/javaparser/javaparser](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/javaparser/javaparser?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

## Features

*   Light weight
*   Performant
*   Easy to use
*   Modifiable AST
*   Code generation
*   Support of comments

## Dependency Management

The project binaries are available in Maven Central.  Just add the following to your maven configuration or tailor to your own dependency management system.

[Please refer to the Migration Guide when upgrading from 2.5.1](https://github.com/javaparser/javaparser/wiki/Migration-Guide)

For Maven: 

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core</artifactId>
    <version>3.2.11</version>
</dependency>
```

For Gradle:

```
compile 'com.github.javaparser:javaparser-core:3.2.11'
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

## Manual

Examples of how to use the library can be found on the [Manual](https://github.com/javaparser/javaparser/wiki/Manual) page of the wiki

## Troubleshooting

First try the [wiki](https://github.com/javaparser/javaparser/wiki).

Didn't find an answer? Try [searching for existing issues](https://github.com/javaparser/javaparser/issues?utf8=%E2%9C%93&q=is%3Aissue%20)

Still nothing? [Open an issue](https://github.com/javaparser/javaparser/issues/new) or [come chat on Gitter](https://gitter.im/javaparser/javaparser)

## Javadoc

The libraries javadoc can be found [here](http://www.javadoc.io/doc/com.github.javaparser/javaparser-core/)

## History

This parser is based on work by Sreenivasa Viswanadha and Júlio Vilmar Gesser. The original project, now inactive, was originally hosted at [Google Code](http://code.google.com/p/javaparser/) and supported only parsing Java 1.5.

The project now supports parsing Java 9 and aims to continue support for features in future versions of the Java language.

## Related projects

[JavaSymbolSolver](https://github.com/javaparser/javasymbolsolver) is a project from the same committers working on JavaParser.
You can use it to calculate the type of JavaParser expressions and connecting references with their declarations. 

From JavaParser other projects have been derived:

* [Walkmod](http://walkmod.com/): a tool to automatically correct violations of code conventions
* [jooby spec](http://jooby.org/doc/spec): analyze and exports [jooby routes](http://jooby.org) to [raml](http://raml.org) and [Swagger](http://swagger.io)

## Credits

This project has been maintained thanks to the joint efforts of many contributors: we are extremely grateful to all of them.

In particular we are thankful to the contributions we received by the [Walkmod](http://walkmod.com/) project which permitted to finalize support for Java 8. The author granted us the permissions to release that code also under the Apache License and we have greatly appreciated that.

## License

JavaParser is available either under the terms of the LGPL License or the Apache License. You as the user are entitled to choose the terms under which adopt JavaParser.

For details about the LGPL License please refer to [LICENSE.LGPL](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.LGPL).

For details about the Apache License please refer to [LICENSE.APACHE](ttps://github.com/javaparser/javaparser/blob/master/LICENSE.APACHE).
