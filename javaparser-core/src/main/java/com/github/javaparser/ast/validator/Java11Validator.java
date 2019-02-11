package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.chunks.VarValidator;

/**
 * This validator validates according to Java 11 syntax rules.
 */
public class Java11Validator extends Java10Validator {
    final Validator varAlsoInLambdaParameters = new SingleNodeTypeValidator<>(VarType.class, new VarValidator(true));

    public Java11Validator() {
        super();
        replace(varOnlyOnLocalVariableDefinitionAndFor, varAlsoInLambdaParameters);
    }
}
