# Java 1.7 japa.parser and Abstract Syntax Tree.
[![Build Status](https://drone.io/github.com/matozoid/javaparser/status.png)](https://drone.io/github.com/matozoid/javaparser)

Copyright (C) 2007 J&uacute;lio Vilmar Gesser

	This program is free software: you can redistribute it and/or modify
	it under the terms of the GNU Lesser General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU Lesser General Public License for more details.

	You should have received a copy of the GNU Lesser General Public License
	along with this program.  If not, see <http://www.gnu.org/licenses/>.

This package contains a Java 1.7 Parser with AST generation and visitor support. 
The AST records the source code structure, javadoc and comments.

## Use JavaParser in my Maven-based project

```
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

If you have problems, please feel free to open an issue.

## Javadoc

Javadoc is available at [http://matozoid.github.io/javaparser/javadoc-current/](http://matozoid.github.io/javaparser/javadoc-current/)

## History

This japa.parser is based on Sreenivasa Viswanadha's Java 1.5 japa.parser.

The project was originally hosted at http://code.google.com/p/javaparser/ but 
seemed dead. This repository at https://github.com/matozoid/javaparser keeps 
the code alive.
