package com.github.javaparser.ast;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.*;
import static java.lang.annotation.RetentionPolicy.SOURCE;

/**
 * Copied from javax.annotation.Generated and reduced a bit.
 * <p>
 * Indicates a part of the code that was generated,
 * and will be overwritten the next time the generators are run.
 */
@Retention(SOURCE)
@Target({PACKAGE, TYPE, ANNOTATION_TYPE, METHOD, CONSTRUCTOR, FIELD,
        LOCAL_VARIABLE, PARAMETER})
public @interface Generated {
    /**
     * The value element must have the name of the code generator.
     * The recommended convention is to use the fully qualified name of the
     * code generator. For example: <code>com.acme.generator.CodeGen</code>.
     */
    String[] value();
}