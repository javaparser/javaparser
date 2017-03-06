package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleRequiresStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithRange;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.utils.SeparatedItemStringBuilder;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.ast.Modifier.*;
import static java.util.Arrays.binarySearch;

/**
 * Verifies that only allowed modifiers are used where modifiers are expected.
 */
public class BaseModifierValidator extends VisitorValidator {
    @Override
    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
        n.getParentNode().ifPresent(parent -> {
            if (parent instanceof CompilationUnit) {
                // top level
                if (n.isInterface()) {
                    validateModifiers(n, reporter, PUBLIC, ABSTRACT, STRICTFP);
                } else {
                    validateModifiers(n, reporter, PUBLIC, ABSTRACT, FINAL, STRICTFP);
                }
            } else if (parent instanceof ClassOrInterfaceDeclaration) {
                // nested
                if (n.isInterface()) {
                    validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, STRICTFP);
                } else {
                    validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, FINAL, STRICTFP);
                }
            } else if (parent instanceof LocalClassDeclarationStmt) {
                if (!n.isInterface()) {
                    // local class
                    validateModifiers(n, reporter, ABSTRACT, FINAL, STRICTFP);
                }
            }
            // Can't validate this class without a context
            super.visit(n, reporter);
        });
    }

    private <T extends NodeWithModifiers<?> & NodeWithRange<?>> void validateModifiers(T n, ProblemReporter reporter, Modifier... allowedModifiers) {
        validateAtMostOneOf(n, reporter, PUBLIC, PROTECTED, PRIVATE);
        validateAtMostOneOf(n, reporter, FINAL, ABSTRACT);
        n.getModifiers().forEach(m -> {
            if (binarySearch(allowedModifiers, m) < 0) {
                reporter.report(n, "'%s' is not allowed here.", m.asString());
            }
        });
    }

    private <T extends NodeWithModifiers<?> & NodeWithRange<?>> void validateAtMostOneOf(T t, ProblemReporter reporter, Modifier... modifiers) {
        List<Modifier> foundModifiers = new ArrayList<>();
        for (Modifier m : modifiers) {
            if (t.getModifiers().contains(m)) {
                foundModifiers.add(m);
            }
        }
        if (foundModifiers.size() > 1) {
            SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder("Can have only one of '", "', '", "'.");
            for (Modifier m : foundModifiers) {
                builder.append(m.asString());
            }
            reporter.report(t, builder.toString());
        }
    }

    // EnumDeclaration
    @Override
    public void visit(EnumDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // AnnotationTypeDeclaration
    @Override
    public void visit(AnnotationDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // AnnotationTypeMemberDeclaration
    @Override
    public void visit(AnnotationMemberDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // ModuleDeclaration
    @Override
    public void visit(ModuleDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // ConstructorDeclaration
    // Parameter in MethodDeclaration or ConstructorDeclaration
    @Override
    public void visit(ConstructorDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // FieldDeclaration
    @Override
    public void visit(FieldDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // MethodDeclaration
    // Parameter in MethodDeclaration or ConstructorDeclaration
    @Override
    public void visit(MethodDeclaration n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // Parameter in LambdaExpr
    @Override
    public void visit(LambdaExpr n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // Parameter in CatchClause
    @Override
    public void visit(CatchClause n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // VariableDeclarationExpr
    @Override
    public void visit(VariableDeclarationExpr n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // ModuleRequiresStmt
    @Override
    public void visit(ModuleRequiresStmt n, ProblemReporter reporter) {
        super.visit(n, reporter);
    }

    // Can't have public, protected, and/or private at the same time.
}
