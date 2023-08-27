package com.github.javaparser.symbolsolver.testingclasses;

@SuppressWarnings("ALL")
public interface InterfaceWithMethods {

    void test();

    abstract void test1();

    default void test2() {

    }

    static void test3() {

    }
}
