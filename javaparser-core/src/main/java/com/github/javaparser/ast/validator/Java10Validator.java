package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.chunks.VarValidator;

/**
 * This validator validates according to Java 10 syntax rules.
 */
public class Java10Validator extends Java9Validator {

    final Validator varOnlyOnLocalVariableDefinitionAndFor = new SingleNodeTypeValidator<>(VarType.class, new VarValidator(false));

    public Java10Validator() {
        super();
        add(varOnlyOnLocalVariableDefinitionAndFor);
        /* There is no validator that validates that "var" is not used in Java 9 and lower, since the parser will never create a VarType node,
           because that is done by the Java10 postprocessor. You can add it by hand, but that is obscure enough to ignore. */
    }
}
