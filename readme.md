## Java Parser and Abstract Syntax Tree

This package contains a Java 1.8 Parser with AST generation and visitor support.

The AST records the source code structure, javadoc and comments. It is also possible to change the AST nodes or create new ones to modify the source code.

[![Join the chat at https://gitter.im/javaparser/javaparser](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/javaparser/javaparser?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

[![Build Status](https://travis-ci.org/javaparser/javaparser.svg?branch=master)](https://travis-ci.org/javaparser/javaparser)

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
    <version>2.0.0</version>
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

The libraries javadoc can be found [here](http://javaparser.github.io/javaparser/javadoc-current/)

## History

This parser is based on Sreenivasa Viswanadha's Java 1.5 parser.

The project was originally hosted at [Google Code](http://code.google.com/p/javaparser/), however support there dwindled.

This repository aims to provide support for issues and add the new Java language features.

## Licence

Offered under the GNU GENERAL PUBLIC LICENSE that can be found [here](https://github.com/javaparser/javaparser/blob/master/COPYING)
