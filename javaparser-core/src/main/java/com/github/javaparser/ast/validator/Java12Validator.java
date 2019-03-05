package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 12 syntax rules.
 */
public class Java12Validator extends Java11Validator {

    public Java12Validator() {
        super();
        remove(noSwitchExpressions);
        remove(onlyOneLabelInSwitchCase);
        remove(noValueBreak);
    }
}
