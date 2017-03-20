package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 1.0 syntax rules.
 */
public class Java1_0Validator extends Validators {
    protected final Validator modifiersWithoutStrictfpAndDefault = new ModifierValidator(false, false);
    protected final Validator noAssertKeyword = new SimpleValidator<>(AssertStmt.class,
            n -> true,
            (n, reporter) -> reporter.report(n, "'assert' keyword is not supported.")
    );
    protected final Validator noInnerClasses = new SimpleValidator<>(ClassOrInterfaceDeclaration.class,
            n -> !n.isTopLevelType(),
            (n, reporter) -> reporter.report(n, "inner classes or interfaces are not supported.")
    );
    protected final Validator noReflection = new SimpleValidator<>(ClassExpr.class,
            n -> true,
            (n, reporter) -> reporter.report(n, "Reflection is not supported.")
    );
    protected final Validator noGenerics = new TreeVisitorValidator() {
        @Override
        public void process(Node node, ProblemReporter reporter) {
            if (node instanceof NodeWithTypeArguments) {
                if(((NodeWithTypeArguments<? extends Node>) node).getTypeArguments().isPresent()){
                    reporter.report(node, "Generics are not supported.");
                }
            }
            if (node instanceof NodeWithTypeParameters) {
                if(((NodeWithTypeParameters<? extends Node>) node).getTypeParameters().isNonEmpty()){
                    reporter.report(node, "Generics are not supported.");
                }
            }
        }
    };

    public Java1_0Validator() {
        super(new CommonValidators());
        add(modifiersWithoutStrictfpAndDefault);
        add(noAssertKeyword);
        add(noInnerClasses);
        add(noReflection);
        add(noGenerics);
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
