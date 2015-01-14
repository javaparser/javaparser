# Java Parser and Abstract Syntax Tree for Java 8.

This package contains a Java 1.8 Parser with AST generation and visitor support.
The AST records the source code structure, javadoc and comments.

[![Build Status](https://drone.io/github.com/javaparser/javaparser/status.png)](https://drone.io/github.com/javaparser/javaparser/latest)

## Use JavaParser in my Maven-based project

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


## How to build

```
mvn javacc:javacc
mvn clean install
```

## Troubleshooting

In the first instance try colsulting the [Wiki](https://github.com/javaparser/javaparser/wiki)

In the second instance please feel free to open an [issue](https://github.com/javaparser/javaparser/issues).

## Javadoc

Javadoc can be found [here](http://javaparser.github.io/javaparser/javadoc-current/)

## History

This parser is based on Sreenivasa Viswanadha's Java 1.5 parser.

The project was originally hosted at [Google Code](http://code.google.com/p/javaparser/), however support there dwindled.

This repository aims to provide support for issues and add the new Java language features.

## Licence

Offered under the GNU GENERAL PUBLIC LICENSE that can be found [here](https://github.com/javaparser/javaparser/blob/master/COPYING)