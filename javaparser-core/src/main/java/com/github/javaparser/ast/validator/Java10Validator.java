package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import com.github.javaparser.ast.type.VarType;

import java.util.Optional;

/**
 * This validator validates according to Java 10 syntax rules.
 */
public class Java10Validator extends Java9Validator {

    protected final Validator varOnlyOnLocalVariableDefinitionAndFor = new SingleNodeTypeValidator<>(VarType.class, (n, reporter) -> {
        Optional<VariableDeclarator> variableDeclarator = n.findParent(VariableDeclarator.class);
        if (!variableDeclarator.isPresent()) {
            reporter.report(n, "\"var\" is not allowed here.");
            return;
        }
        variableDeclarator.ifPresent(vd -> {
            Optional<Node> container = vd.getParentNode();
            if (!container.isPresent()) {
                reporter.report(n, "\"var\" is not allowed here.");
                return;
            }
            container.ifPresent(c -> {
                boolean positionIsFine = c instanceof ForStmt || c instanceof ForeachStmt || c instanceof VariableDeclarationExpr;
                if (!positionIsFine) {
                    reporter.report(n, "\"var\" is not allowed here.");
                }
            });
        });
    });

    public Java10Validator() {
        super();
        add(varOnlyOnLocalVariableDefinitionAndFor);
        /* There is no validator that validates that "var" is not used in Java 9 and lower, since the parser will never create a VarType node,
           because that is done by the Java10 postprocessor. You can add it by hand, but that is obscure enough to ignore. */
    }
}
