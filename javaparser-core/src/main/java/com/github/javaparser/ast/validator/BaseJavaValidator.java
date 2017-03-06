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
                            reporter.report(n, "Try has no finally, no catch, and no resources");
                        }
                        super.visit(n, reporter);
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (!n.isInterface() && n.getExtendedTypes().size() > 1) {
                            reporter.report(n.getExtendedTypes(1), "A class cannot extend more than one other class");
                        }
                        super.visit(n, reporter);
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface() && !n.getImplementedTypes().isEmpty()) {
                            reporter.report(n.getImplementedTypes(0), "An interface cannot implement other interfaces");
                        }
                        super.visit(n, reporter);
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface()) {
                            n.getMembers().forEach(mem -> {if(mem instanceof InitializerDeclaration){reporter.report("An interface cannot have initializers", mem);}});
                        }
                        super.visit(n, reporter);
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (n.isInterface()) {
                            n.getMethods().forEach(m -> {
                                if (m.isDefault() && !m.getBody().isPresent()) {
                                    reporter.report("\"default\" methods must have a body", m);
                                }
                            });
                        }
                        super.visit(n, reporter);
                    }
                },
                new VisitorValidator() {
                    @Override
                    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
                        if (!n.isInterface()) {
                            n.getMethods().forEach(m -> {
                                if (m.isDefault()) {
                                    reporter.report("A class cannot have default members", m);
                                }
                            });
                        }
                        super.visit(n, reporter);
                    }
                },
                new BaseModifierValidator()
        );
    }
}
