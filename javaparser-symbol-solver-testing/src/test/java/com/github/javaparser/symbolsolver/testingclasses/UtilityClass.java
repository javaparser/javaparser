package com.github.javaparser.symbolsolver.testingclasses;

import java.util.concurrent.Callable;

public class UtilityClass {
    public static void method(SomeClass.InnerEnum e) {

    }

    public static void method(Runnable lambda) {

    }

    public static <T> void method(Callable<T> lambda) {

    }
}
