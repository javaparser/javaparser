package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.UnderscoreKeywordValidator;

/**
 * This validator validates according to Java 9 syntax rules.
 */
public class Java9Validator extends Java8Validator {
    protected Validator underscoreKeywordValidator = new UnderscoreKeywordValidator();

    public Java9Validator() {
        super();
        add(underscoreKeywordValidator);
        // TODO validate modules
    }
}
