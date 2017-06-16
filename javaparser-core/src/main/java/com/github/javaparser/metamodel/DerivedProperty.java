package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

/**
 * Indicate a derived property of a Node,
 * meaning it does supply useful information,
 * but it does so by taking information from other properties.
 * (Used during generation of the meta model.)
 */
@Retention(RUNTIME)
@Target(METHOD)
public @interface DerivedProperty {
}
