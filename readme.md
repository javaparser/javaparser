## Java Parser and Abstract Syntax Tree

This package contains a Java 1.8 Parser with AST generation and visitor support.

The AST records the source code structure, javadoc and comments. It is also possible to change the AST nodes or create new ones to modify the source code.

[![Maven Central](https://img.shields.io/maven-central/v/com.github.javaparser/javaparser-core.svg)](http://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22com.github.javaparser%22%20AND%20a%3A%22javaparser-core%22)
[![Build Status](https://travis-ci.org/javaparser/javaparser.svg?branch=master)](https://travis-ci.org/javaparser/javaparser)
[![Coverage Status](https://coveralls.io/repos/javaparser/javaparser/badge.svg?branch=master&service=github)](https://coveralls.io/github/javaparser/javaparser?branch=master)
[![Join the chat at https://gitter.im/javaparser/javaparser](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/javaparser/javaparser?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

## Features

*   Light weight
*   Performant
*   Easy to use
*   Modifiable AST
*   Create AST from scratch
*   Support of comments

## Dependency Management

The project binaries are available in Maven Central.  Just add the following to your maven configuration or taylor to your own dependency management system.

Current 1.8 Release

```xml
<dependency>
    <groupId>com.github.javaparser</groupId>
    <artifactId>javaparser-core</artifactId>
    <version>2.3.0</version>
</dependency>
```

Final 1.7 Release

```xml
<dependency>
    <groupId>com.google.code.javaparser</groupId>
    <artifactId>javaparser</artifactId>
    <version>1.0.11</version>
</dependency>
```

## How To Compile Sources

If you have checkout the project from GitHub you can build the project with maven using:

```
mvn clean install
```

If you checkout the sources and want to view the project in an IDE, it is best to generate the additional source files; otherwise you will get many compilation complaints in the IDE

```
mvn javacc:javacc
```

## Manual

Examples of how to use the library can be found on the [Manual](https://github.com/javaparser/javaparser/wiki/Manual) page of the wiki

## Troubleshooting

In the first instance try the [wiki](https://github.com/javaparser/javaparser/wiki)

In the second instance please feel free to open an [issue](https://github.com/javaparser/javaparser/issues).

## Javadoc

The libraries javadoc can be found [here](http://www.javadoc.io/doc/com.github.javaparser/javaparser-core/)

## History

This parser is based on work by Sreenivasa Viswanadha and Júlio Vilmar Gesser. The original project, now inactive, was originally hosted at [Google Code](http://code.google.com/p/javaparser/) and supported only parsing Java 1.5.

The project now supports parsing Java 1.8 and aims to continue support for features in future versions of the Java language.

## Related projects

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
