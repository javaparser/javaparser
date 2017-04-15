package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Indicate an internal property of a Node,
 * meaning it is not part of the meta model.
 * (Used during generation of the meta model.)
 */
@Retention(value = RetentionPolicy.RUNTIME)
public @interface InternalProperty {
}
