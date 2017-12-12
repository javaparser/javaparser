package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

/**
 * Indicate an optional property of a Node.
 * (Used during generation of the meta model.)
 */
@Retention(RUNTIME)
@Target(FIELD)
public @interface OptionalProperty {
}
