package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleRequiresStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithRange;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.utils.SeparatedItemStringBuilder;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.ast.Modifier.*;


/**
 * Verifies that only allowed modifiers are used where modifiers are expected.
 */
public class BaseModifierValidator extends VisitorValidator {
    @Override
    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
        if (n.isInterface()) {
            validateInterfaceModifiers(n, reporter);
        } else {
            validateClassModifiers(n, reporter);
        }
        super.visit(n, reporter);
    }

    private void validateClassModifiers(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, ABSTRACT, FINAL, STRICTFP);
        } else if (n.isNestedType()) {
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, FINAL, STRICTFP);
        } else if (n.isLocalClassDeclaration()) {
            validateModifiers(n, reporter, ABSTRACT, FINAL, STRICTFP);
        }
    }

    private void validateInterfaceModifiers(TypeDeclaration<?> n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, ABSTRACT, STRICTFP);
        } else if (n.isNestedType()) {
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, STRICTFP);
        }
    }

    @Override
    public void visit(EnumDeclaration n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, STRICTFP);
        } else if (n.isNestedType()) {
            // nested
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, STATIC, STRICTFP);
        }
        super.visit(n, reporter);
    }

    // AnnotationTypeDeclaration
    @Override
    public void visit(AnnotationDeclaration n, ProblemReporter reporter) {
        validateInterfaceModifiers(n, reporter);
        super.visit(n, reporter);
    }

    // AnnotationTypeMemberDeclaration
    @Override
    public void visit(AnnotationMemberDeclaration n, ProblemReporter reporter) {
        validateModifiers(n, reporter, PUBLIC, ABSTRACT);
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
        validateModifiers(n, reporter, TRANSITIVE, STATIC);
        super.visit(n, reporter);
    }

    private <T extends NodeWithModifiers<?> & NodeWithRange<?>> void validateModifiers(T n, ProblemReporter reporter, Modifier... allowedModifiers) {
        validateAtMostOneOf(n, reporter, PUBLIC, PROTECTED, PRIVATE);
        validateAtMostOneOf(n, reporter, FINAL, ABSTRACT);
        n.getModifiers().forEach(m -> {
            if (!arrayContains(allowedModifiers, m)) {
                reporter.report(n, "'%s' is not allowed here.", m.asString());
            }
        });
    }

    private boolean arrayContains(Object[] items, Object searchItem) {
        for (Object o : items) {
            if (o == searchItem) {
                return true;
            }
        }
        return false;
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

}
