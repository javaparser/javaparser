package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 1.0 syntax rules.
 */
public class Java1_0Validator extends Validators {
    protected final Validator modifiersWithoutStrictfp = new ModifierValidator(false);
    protected final Validator noAssertKeyword = new SimpleValidator<>(AssertStmt.class,
            n -> true,
            (n, reporter) -> reporter.report(n, "'assert' keyword is not supported")
    );
    protected final Validator noInnerClasses = new SimpleValidator<>(ClassOrInterfaceDeclaration.class,
            n -> !n.isTopLevelType(),
            (n, reporter) -> reporter.report(n, "inner classes or interfaces are not supported")
    );

    public Java1_0Validator() {
        super(new CommonValidators());
        add(modifiersWithoutStrictfp);
        add(noAssertKeyword);
        add(noInnerClasses);
        // TODO validate "no reflection"
        // TODO validate "no generics"
        // TODO validate "no annotations"
        // TODO validate "no enums"
        // TODO validate "no varargs"
        // TODO validate "no for-each"
        // TODO validate "no static imports"
        // TODO validate "no strings in switch"
        // TODO validate "no resource management in try statement"
        // TODO validate "no binary integer literals"
        // TODO validate "no underscores in numeric literals"
        // TODO validate "no multi-catch"
        // TODO validate "no lambdas"
        // TODO validate "no modules"
        // TODO validate "no default interface methods"
        // TODO validate "no private interface methods"
    }
}
