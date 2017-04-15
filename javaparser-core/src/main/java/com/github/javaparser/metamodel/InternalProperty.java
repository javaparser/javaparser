package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

/**
 * Indicate an internal property of a Node,
 * meaning it is not part of the meta model.
 * (Used during generation of the meta model.)
 */
@Retention(RUNTIME)
@Target(FIELD)
public @interface InternalProperty {
}
