# JavaSymbolSolver

[![Maven Central](https://img.shields.io/maven-central/v/me.tomassetti/java-symbol-solver-core.svg)](http://search.maven.org/#search%7Cgav%7C1%7Cg%3A%22me.tomassetti%22%20AND%20a%3A%22java-symbol-solver-core%22)
[![Build Status](https://travis-ci.org/javaparser/javasymbolsolver.svg?branch=master)](https://travis-ci.org/javaparser/javasymbolsolver)

A Symbol Solver for Java built on top of [JavaParser](https://github.com/javaparser/javaparser/) from the same team of committers.

## How this complement JavaParser?

JavaParser is a parser: given a source file it recognizes the different syntatic
element and produce an Abstract Syntax Tree (AST).

JavaSymbolSolver analyzes that AST and find the declarations connected to each element.

`foo` in the AST is just a name, JavaSymbolSolver can tell you if it refers to a parameter, a local variable, a field. It can also give you the type, tell you where
the element has been defined and so on.

## What can I use it for?

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

## How can I use it? Show me some code!

Take a look at `JavaParserFacade`. For example you can use it to find the type of an expression:

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

In the tests you can find an example of instantiating `TypeSolver`s:

```java
CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
combinedTypeSolver.add(new JreTypeSolver());
combinedTypeSolver.add(new JavaParserTypeSolver(new File("src/test/resources/javaparser_src/proper_source")));
combinedTypeSolver.add(new JavaParserTypeSolver(new File("src/test/resources/javaparser_src/generated")));
```

Typically to analize a project you want to create one instance of `JavaParserTypeSolver` for each source directory, one instance of `JarTypeSolver` for each dependency and one `JreTypeSolver` then you can combine all of them in a `CombinedTypeSolver` and pass that around.

[Tutorial on resolving method calls](http://tomassetti.me/resolve-method-calls-using-java-symbol-solver/)

_We plan to write soon more examples and tutorials._

## Status of the project

This project is more recent of JavaParser but it has been receiving some attention and
it has been improving a lot recently.

It supports all features of Java 8 (lambdas, generic, type inference, etc.). 
Of course we expect some bugs to emerge from time to time but we are committed to help users solve them as soon as possible.

It has been also used in a commercial product from [Coati](https://www.coati.io/).

## License

This code is available under the Apache License.

## Development

We use Travis to ensure our tests are passing all the time.

The _dev-files_ dir contains configurations for the Eclipse and the IDEA formatters (I took them from the JavaParser project, thanks guys!).

The project is structured in this way:

* We have nodes that wrap the JavaParser nodes (but can also wrap Javassist or JRE nodes)
* The nodes contain all the information of the AST
* Context classes contain the logic to solve methods, symbols and types in the respective context.
* Default fallback behavior: ask the parent context for help (so if a variable identifier cannot be solved inside a MethodContext the underlying ClassDeclarationContext is asked and maybe we find out that the identifier actually refers to a field.

A more detailed description of the architecture of the project is available in [Design.MD](https://github.com/javaparser/javasymbolsolver/blob/master/Design.MD)

## Contributing

I would absolutely love every possible kind of contributions: if you have questions, ideas, need help or want to propose a change just open an issue. Pull-requests are greatly appreciated.

Thanks to Malte Langkabel, Ayman Abdelghany, Evan Rittenhouse, Rachel Pau, Pavel Eremeev, Simone Basso and Rafael Vargas for their contributions!

The project has been created by [Federico Tomassetti](http://tomassetti.me) and it is currently co-maintained by the JavaParser team.
