package com.github.javaparser.metamodel;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Indicate a derived property of a Node.
 */
@Retention(value = RetentionPolicy.RUNTIME)
public @interface DerivedProperty {
}
