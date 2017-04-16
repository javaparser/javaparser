package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

/**
 * Indicate that leaving this property empty does not lead to a correct AST.
 * Empty means either empty string or empty collection.
 * (Used during generation of the meta model.)
 */
@Retention(RUNTIME)
@Target({FIELD, METHOD})
public @interface NonEmptyProperty {
}
