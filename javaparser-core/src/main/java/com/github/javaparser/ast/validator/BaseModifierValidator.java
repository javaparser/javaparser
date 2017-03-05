package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleRequiresStmt;
import com.github.javaparser.ast.stmt.CatchClause;

/**
 * Verifies that only allowed modifiers are used where modifiers are expected.
 */
public class BaseModifierValidator extends VisitorValidator {
    // ClassOrInterfaceDeclaration
    @Override
    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // EnumDeclaration
    @Override
    public void visit(EnumDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // AnnotationTypeDeclaration
    @Override
    public void visit(AnnotationDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // AnnotationTypeMemberDeclaration
    @Override
    public void visit(AnnotationMemberDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // ModuleDeclaration
    @Override
    public void visit(ModuleDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // ConstructorDeclaration
    // Parameter in MethodDeclaration or ConstructorDeclaration
    @Override
    public void visit(ConstructorDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // FieldDeclaration
    @Override
    public void visit(FieldDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // MethodDeclaration
    // Parameter in MethodDeclaration or ConstructorDeclaration
    @Override
    public void visit(MethodDeclaration n, ProblemReporter arg) {
        super.visit(n, arg);
    }
    
    // Parameter in LambdaExpr
    @Override
    public void visit(LambdaExpr n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // Parameter in CatchClause
    @Override
    public void visit(CatchClause n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // VariableDeclarationExpr
    @Override
    public void visit(VariableDeclarationExpr n, ProblemReporter arg) {
        super.visit(n, arg);
    }

    // ModuleRequiresStmt
    @Override
    public void visit(ModuleRequiresStmt n, ProblemReporter arg) {
        super.visit(n, arg);
    }
}
