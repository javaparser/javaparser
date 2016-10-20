# Architecture and Design

This document describe the architecture and design of JavaSymbolSolver.

## Goal of the project

The basic idea is to be able to resolve all sorts of symbols:

* field, variable, parameter references
* type references
* calculate the type of expressions
* determine which methods are invoked out of the several overload possible

# Organization

The project is divided in four modules:

* **model**: it contains the interfaces of all declarations used by JavaSymbolSolver such as _ClassDeclaration_, _ParameterDeclaration_, _MethodDeclaration_, etc.
* **logic**: it contains general logic to operate on declarations, for example to perform method resolution
* **core**: it contains most of the implementation including all the implementation of all the interfaces for source code (using JavaParser), compiled code (using Javassist) and JRE standard libraries (using reflection)
* **examples**: examples of possible usages of JavaSymbolSolver
 
# Strategy

## Resolving types

Given a reference to a declared type such as `Object`, `java.lang.String`, or `Foo` we need to figure out to which declaration
it corresponds. Declarations can derive from three sources:

* Compiled classes (class files contained in a directory or a JAR file)
* Java source code
* Classes from the JRE for which we do not have JAR classes. We access them through reflection

To each of these types correspond an implementation of a `TypeSolver`.

We consider the way Java resolve types (considering imports, using simple names for classes in the same package, usage 
of canonical names) and we look at the different sources we have to find the types definitions.

# Resources

TODO: link to articles on tomassetti.me
