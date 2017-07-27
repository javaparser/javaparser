package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 1.2 syntax rules.
 */
public class Java1_2Validator extends Java1_1Validator {
    protected final Validator modifiersWithoutDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods = new ModifierValidator(true, false, false);
    protected final Validator strictfpNotAllowed = new ReservedKeywordValidator("strictfp");
    
    public Java1_2Validator() {
        super();
        replace(modifiersWithoutStrictfpAndDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods, modifiersWithoutDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods);
        add(strictfpNotAllowed);
    }
}
