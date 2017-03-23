package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java8Validator extends Java7Validator {
    protected final Validator modifiersWithoutPrivateInterfaceMethods = new ModifierValidator(true, true, false);
    protected final Validator defaultMethodsInInterface = new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class,
            (n, reporter) -> {
                if (n.isInterface()) {
                    n.getMethods().forEach(m -> {
                        if (m.isDefault() && !m.getBody().isPresent()) {
                            reporter.report(m, "'default' methods must have a body.");
                        }
                    });
                }
            }
    );

    public Java8Validator() {
        super();
        replace(modifiersWithoutDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods, modifiersWithoutPrivateInterfaceMethods);
        add(defaultMethodsInInterface);
        remove(noLambdas);

        // TODO validate more annotation locations http://openjdk.java.net/jeps/104
        // TODO validate repeating annotations http://openjdk.java.net/jeps/120
    }
}
