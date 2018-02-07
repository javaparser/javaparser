package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.type.VarType;

/**
 * This validator validates according to Java 10 syntax rules.
 */
public class Java10Validator extends Java9Validator {

    protected final Validator varOnlyOnLocalVariableDefinitionAndFor = new SingleNodeTypeValidator<>(VarType.class, (n, reporter) -> {
        // TODO issue 1407
    });

    public Java10Validator() {
        super();
        add(varOnlyOnLocalVariableDefinitionAndFor);
        /* There is no validator that validates that "var" is not used in Java 9 and lower, since the parser will never create a VarType node,
           because that is done by the Java10 postprocessor. You can add it by hand, but that is obscure enough to ignore. */
    }
}
