package com.github.javaparser.ast.validator.chunks;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.validator.SimpleValidator;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validators;

import java.util.Optional;

/**
 * Contains validations that are valid for every Java version.
 */
public class CommonValidators extends Validators {
    public CommonValidators() {
        super(
                new SimpleValidator<>(ClassOrInterfaceDeclaration.class,
                        n -> !n.isInterface() && n.getExtendedTypes().size() > 1,
                        (n, reporter) -> reporter.report(n.getExtendedTypes(1), "A class cannot extend more than one other class.")
                ),
                new SimpleValidator<>(ClassOrInterfaceDeclaration.class,
                        n -> n.isInterface() && !n.getImplementedTypes().isEmpty(),
                        (n, reporter) -> reporter.report(n.getImplementedTypes(0), "An interface cannot implement other interfaces.")
                ),
                new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class,
                        (n, reporter) -> {
                            if (n.isInterface()) {
                                n.getMembers().forEach(mem -> {
                                    if (mem instanceof InitializerDeclaration) {
                                        reporter.report(mem, "An interface cannot have initializers.");
                                    }
                                });
                            }
                        }
                ),
                new SingleNodeTypeValidator<>(AssignExpr.class,
                        (n, reporter) -> {
                            // https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.26
                            Expression target = n.getTarget();
                            while (target instanceof EnclosedExpr) {
                                Optional<Expression> inner = ((EnclosedExpr) target).getInner();
                                if (!inner.isPresent()) {
                                    reporter.report(n.getTarget(), "Illegal left hand side of an assignment.");
                                    return;
                                }
                                target = inner.get();
                            }
                            if (target instanceof NameExpr
                                    || target instanceof ArrayAccessExpr
                                    || target instanceof FieldAccessExpr) {
                                return;
                            }
                            reporter.report(n.getTarget(), "Illegal left hand side of an assignment.");
                        }
                )
        );
    }
}
