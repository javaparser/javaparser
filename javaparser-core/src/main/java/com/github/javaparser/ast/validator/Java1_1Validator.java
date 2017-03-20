package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.InnerClassesValidator;

/**
 * This validator validates according to Java 1.1 syntax rules.
 */
public class Java1_1Validator extends Java1_0Validator {
    protected final Validator innerClasses = new InnerClassesValidator();

    public Java1_1Validator() {
        super();
        replace(noInnerClasses, innerClasses);
        // TODO validate reflection
    }
}
