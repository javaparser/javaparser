package com.github.javaparser.symbolsolver.testingclasses;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.invoke.LambdaMetafactory;
import java.lang.invoke.MethodHandle;
import java.util.concurrent.TimeUnit;

@interface NestedAnnotation {

}

@Target({ElementType.TYPE, ElementType.METHOD, ElementType.CONSTRUCTOR})
@Retention(RetentionPolicy.SOURCE)
public @interface TargetType {
    Class<?>[] packagesOf() default {MethodHandle.class};

    Class<?> clazz() default LambdaMetafactory.class;

    TimeUnit unit() default TimeUnit.HOURS;

    NestedAnnotation nestedAnnotation() default @NestedAnnotation;
}