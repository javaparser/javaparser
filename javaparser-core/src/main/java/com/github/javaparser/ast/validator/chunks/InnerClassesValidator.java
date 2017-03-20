package com.github.javaparser.ast.validator.chunks;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validators;

/**
 * All validations concerning inner classes.
 */
public class InnerClassesValidator extends Validators {
    public InnerClassesValidator() {
        super(
                new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class,
                        (n, reporter) -> n.getParentNode().ifPresent(p -> {
                            if (p instanceof LocalClassDeclarationStmt && n.isInterface())
                                reporter.report(n, "There is no such thing as a local interface.");
                        })
                )
        );
    }
}
