package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;

import java.util.Optional;

/**
 * This validator validates according to Java 5 syntax rules.
 */
public class Java5Validator extends Java1_4Validator {
    final Validator genericsWithoutDiamondOperator = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof NodeWithTypeArguments) {
            Optional<NodeList<Type>> typeArguments = ((NodeWithTypeArguments<? extends Node>) node).getTypeArguments();
            if (typeArguments.isPresent() && typeArguments.get().isEmpty()) {
                reporter.report(node, "The diamond operator is not supported.");
            }
        }
    });

    protected final Validator noPrimitiveGenericArguments = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof NodeWithTypeArguments) {
            Optional<NodeList<Type>> typeArguments = ((NodeWithTypeArguments<? extends Node>) node).getTypeArguments();
            typeArguments.ifPresent(types -> types.forEach(ty -> {
                if (ty instanceof PrimitiveType) {
                    reporter.report(node, "Type arguments may not be primitive.");
                }
            }));
        }
    });

    // Enhanced for statements were introduced in Java 5. There must be exactly one declared variable, and the only
    // allowed modifier is FINAL.
    final Validator forEachStmt = new SingleNodeTypeValidator<>(ForEachStmt.class, (node, reporter) -> {
        VariableDeclarationExpr declaration = node.getVariable();
        // assert that the variable declaration expression has exactly one variable declarator
        if (declaration.getVariables().size() != 1) {
            reporter.report(node, "A foreach statement's variable declaration must have exactly one variable " +
                    "declarator. Given: " + declaration.getVariables().size() + ".");
        }
    });

    final Validator enumNotAllowed = new ReservedKeywordValidator("enum");

    public Java5Validator() {
        super();
        replace(noGenerics, genericsWithoutDiamondOperator);
        add(noPrimitiveGenericArguments);
        add(enumNotAllowed);
        add(forEachStmt);

        // TODO validate annotations on classes, fields and methods but nowhere else
        // The following is probably too simple.
        remove(noAnnotations);

        remove(noEnums);
        remove(noVarargs);
        remove(noForEach);
        remove(noStaticImports);
    }
}
