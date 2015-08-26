# JavaSymbolSolver

[![Build Status](https://travis-ci.org/ftomassetti/java-symbol-solver.svg?branch=master)](https://travis-ci.org/ftomassetti/java-symbol-solver)

A Symbol Solver for Java built on top of [JavaParser](https://github.com/javaparser/javaparser/).

## What can you use a Symbol Solver for?

A Symbol Solver can associate a symbol in your code to its declaration. This is necessary to verify the type of an expression or to find the usage of a symbol (like a field or a local variable):

Consider this:

```java
    int a = 0;
    while (true) {
        String a = "hello!";
        Object foo = a + 1;
    }
```

In the expression `a + 1` a parser (like JavaParser) is not able to tell us to which definition of `a` we are referring to and consequently it cannot tell us the type of `a`. The JavaSymbolSolver is able to do so.

## How can I use it?

Take a look at `JavaParserFacade`. For exaple you can use it to find the type of an expression:

```java
Node node = <get this node by parsing source code with JavaParser>
TypeUsage typeOfTheNode = JavaParserFacade.get(typeSolver).getType(node);
```

Easy, right?

The only configuration that it requires is part of the `TypeSolver` instance to pass it. A `TypeSolver` is the mechanism that is used to find the classes referenced in your code. For example your class could import or extend a given class and the `TypeSolver` will find it and build a model of it, later used to solve symbols. Basically there are four `TypeSolver`:
* `JavaParserTypeSolver`: look for the type in a directory of source files
* `JarTypeSolver`: look for the type in a JAR file
* `JreTypeSolver`: look for the type using reflection. This is needed because some classes are not available in any other way (for example the `Object` class). However this should be used exclusively for files in the java or javax packages
* `CombinedTypeSolver`: permits to combine several instances of `TypeSolver`s

In the tests you can find an example of instanting `TypeSolver`s:

```java
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(new File("src/test/resources/javaparser_src/proper_source")));
        combinedTypeSolver.add(new JavaParserTypeSolver(new File("src/test/resources/javaparser_src/generated")));
```

Typically to analize a project you want to create one instance of `JavaParserTypeSolver` for each source directory, one instance of `JarTypeSolver` for each dependency and one `JreTypeSolver` then you can combine all of them in a `CombinedTypeSolver` and pass that around.

_We plan to write soon more examples and tutorials._

## Status of the project

This project is young but we have already tried it on significant projects and it is doing well so far. It supports all features of Java 8 (lambdas, generic, type inference, etc.). Of course we expect some bugs to emerge from time to time but we are committed to help users solve them as soon as possible.

## License

This code is available under the Apache License.

## Contributing

I would absolutely love every possible kind of contributions: if you have questions, ideas, need help or want to propose a change just open an issue. Pull-requests are greatly appreciated.

