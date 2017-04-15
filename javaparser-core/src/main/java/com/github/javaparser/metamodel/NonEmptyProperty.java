package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Indicate that leaving this property empty does not lead to a correct AST.
 * (Used during generation of the meta model.)
 */
@Retention(value = RetentionPolicy.RUNTIME)
public @interface NonEmptyProperty {
}
