# java-symbol-solver
A Symbol Solver for Java built on top of JavaParser

## Goal of the project

The goal of the project is to complement JavaParser with symbol resolution, so that more advanced tools can be built
on top of it.

Consider this:

```java
    int a = 0;
    while (true) {
        String a = "hello!";
        Object foo = a + 1;
    }
```

In the expression `a + 1` JavaParser is not able to tell us to which definition of `a` we are referring to and consequently
it cannot tell us the type of `a`. The java-symbol-solver will permit to do that.

## Examples

