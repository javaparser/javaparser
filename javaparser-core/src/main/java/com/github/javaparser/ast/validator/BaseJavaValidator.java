package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.TryStmt;

/**
 * Contains validations that are valid for every Java version.
 * Used by default by the static JavaParser methods.
 */
public class BaseJavaValidator extends Validators {
    public BaseJavaValidator() {
        super(
                new VisitorValidator() {
                    @Override
                    public void visit(TryStmt n, ProblemReporter reporter) {
                        if (n.getCatchClauses().isEmpty()
                                && n.getResources().isEmpty()
                                && !n.getFinallyBlock().isPresent()) {
                            reporter.report("Try has no finally, no catch, and no resources", n);
                        }
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (!n.isInterface() && n.getExtendedTypes().size() > 1) {
                            reporter.report("A class cannot extend more than one other class", n.getExtendedTypes(1));
                        }
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface() && !n.getImplementedTypes().isEmpty()) {
                            reporter.report("An interface cannot implement other interfaces", n.getImplementedTypes(0));
                        }
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface()) {
                            new VisitorValidator() {
                                public void visit(InitializerDeclaration n, ProblemReporter reporter1) {
                                    reporter.report("An interface cannot have initializers", n);
                                }
                            }.validate(n, reporter);
                        }
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface()) {
                            new VisitorValidator() {
                                public void visit(MethodDeclaration n, ProblemReporter reporter1) {
                                    if (n.isDefault() && !n.getBody().isPresent()) {
                                        reporter.report("\"default\" methods must have a body", n);
                                    }
                                }
                            }.validate(n, reporter);
                        }
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (!n.isInterface()) {
                            new VisitorValidator() {
                                public void visit(MethodDeclaration n, ProblemReporter reporter1) {
                                    if (n.isDefault()) {
                                        reporter.report("A class cannot have default members", n);
                                    }
                                }
                            }.validate(n, reporter);
                        }
                    }
                },
                new BaseModifierValidator()
        );
    }
}
