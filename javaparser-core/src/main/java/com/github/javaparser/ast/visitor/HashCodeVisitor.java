package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

public class HashCodeVisitor implements GenericVisitor<Integer, Void> {

    public Integer visit(AnnotationDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getMembers() == null ? 0 : n.getMembers().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(AnnotationMemberDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getDefaultValue() == null ? 0 : n.getDefaultValue().hashCode());
    }

    public Integer visit(ArrayAccessExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getIndex() == null ? 0 : n.getIndex().hashCode());
    }

    public Integer visit(ArrayCreationExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getInitializer() == null ? 0 : n.getInitializer().hashCode()) * 31 + (n.getLevels() == null ? 0 : n.getLevels().hashCode()) * 31 + (n.getElementType() == null ? 0 : n.getElementType().hashCode());
    }

    public Integer visit(ArrayCreationLevel n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getDimension() == null ? 0 : n.getDimension().hashCode());
    }

    public Integer visit(ArrayInitializerExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getValues() == null ? 0 : n.getValues().hashCode());
    }

    public Integer visit(ArrayType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getComponentType() == null ? 0 : n.getComponentType().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(AssertStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getMessage() == null ? 0 : n.getMessage().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getCheck() == null ? 0 : n.getCheck().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(AssignExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getOperator() == null ? 0 : n.getOperator().hashCode()) * 31 + (n.getTarget() == null ? 0 : n.getTarget().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(BadImportDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(BinaryExpr n, Void arg) {
        return (n.getRight() == null ? 0 : n.getRight().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getOperator() == null ? 0 : n.getOperator().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getLeft() == null ? 0 : n.getLeft().hashCode());
    }

    public Integer visit(BlockComment n, Void arg) {
        return (n.getCommentedNode() == null ? 0 : n.getCommentedNode().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getContent() == null ? 0 : n.getContent().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(BlockStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getStatements() == null ? 0 : n.getStatements().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(BooleanLiteralExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getValue() ? 1 : 0) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(BreakStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode());
    }

    public Integer visit(CastExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(CatchClause n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getParameter() == null ? 0 : n.getParameter().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getCatchBlock() == null ? 0 : n.getCatchBlock().hashCode());
    }

    public Integer visit(CharLiteralExpr n, Void arg) {
        return (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(ClassExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode());
    }

    public Integer visit(ClassOrInterfaceDeclaration n, Void arg) {
        return (n.isInterface() ? 1 : 0) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getImplementedTypes() == null ? 0 : n.getImplementedTypes().hashCode()) * 31 + (n.getTypeParameters() == null ? 0 : n.getTypeParameters().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getMembers() == null ? 0 : n.getMembers().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getExtendedTypes() == null ? 0 : n.getExtendedTypes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(ClassOrInterfaceType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getScope() == null ? 0 : n.getScope().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(CompilationUnit n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getImports() == null ? 0 : n.getImports().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getPackageDeclaration() == null ? 0 : n.getPackageDeclaration().hashCode()) * 31 + (n.getTypes() == null ? 0 : n.getTypes().hashCode());
    }

    public Integer visit(ConditionalExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getCondition() == null ? 0 : n.getCondition().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getThenExpr() == null ? 0 : n.getThenExpr().hashCode()) * 31 + (n.getElseExpr() == null ? 0 : n.getElseExpr().hashCode());
    }

    public Integer visit(ConstructorDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getThrownExceptions() == null ? 0 : n.getThrownExceptions().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode()) * 31 + (n.getTypeParameters() == null ? 0 : n.getTypeParameters().hashCode()) * 31 + (n.getParameters() == null ? 0 : n.getParameters().hashCode());
    }

    public Integer visit(ContinueStmt n, Void arg) {
        return (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(DoStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getCondition() == null ? 0 : n.getCondition().hashCode());
    }

    public Integer visit(DoubleLiteralExpr n, Void arg) {
        return (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(EmptyMemberDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(EmptyStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(EnclosedExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getInner() == null ? 0 : n.getInner().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(EnumConstantDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getArguments() == null ? 0 : n.getArguments().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getClassBody() == null ? 0 : n.getClassBody().hashCode());
    }

    public Integer visit(EnumDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getMembers() == null ? 0 : n.getMembers().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getEntries() == null ? 0 : n.getEntries().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getImplementedTypes() == null ? 0 : n.getImplementedTypes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getArguments() == null ? 0 : n.getArguments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode()) * 31 + (n.isThis() ? 1 : 0);
    }

    public Integer visit(ExpressionStmt n, Void arg) {
        return (n.getExpression() == null ? 0 : n.getExpression().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(FieldAccessExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getField() == null ? 0 : n.getField().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getScope() == null ? 0 : n.getScope().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode());
    }

    public Integer visit(FieldDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getVariables() == null ? 0 : n.getVariables().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(ForStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getCompare() == null ? 0 : n.getCompare().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getInitialization() == null ? 0 : n.getInitialization().hashCode()) * 31 + (n.getUpdate() == null ? 0 : n.getUpdate().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode());
    }

    public Integer visit(ForeachStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getIterable() == null ? 0 : n.getIterable().hashCode()) * 31 + (n.getVariable() == null ? 0 : n.getVariable().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(IfStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getThenStmt() == null ? 0 : n.getThenStmt().hashCode()) * 31 + (n.getElseStmt() == null ? 0 : n.getElseStmt().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getCondition() == null ? 0 : n.getCondition().hashCode());
    }

    public Integer visit(InitializerDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.isStatic() ? 1 : 0) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getBlock() == null ? 0 : n.getBlock().hashCode());
    }

    public Integer visit(InstanceOfExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode());
    }

    public Integer visit(IntegerLiteralExpr n, Void arg) {
        return (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(IntersectionType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getElements() == null ? 0 : n.getElements().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(JavadocComment n, Void arg) {
        return (n.getCommentedNode() == null ? 0 : n.getCommentedNode().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getContent() == null ? 0 : n.getContent().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(LabeledStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getLabel() == null ? 0 : n.getLabel().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getStatement() == null ? 0 : n.getStatement().hashCode());
    }

    public Integer visit(LambdaExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.isEnclosingParameters() ? 1 : 0) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getParameters() == null ? 0 : n.getParameters().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode());
    }

    public Integer visit(LineComment n, Void arg) {
        return (n.getCommentedNode() == null ? 0 : n.getCommentedNode().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getContent() == null ? 0 : n.getContent().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(LongLiteralExpr n, Void arg) {
        return (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(MarkerAnnotationExpr n, Void arg) {
        return (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(MemberValuePair n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(MethodCallExpr n, Void arg) {
        return (n.getScope() == null ? 0 : n.getScope().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getArguments() == null ? 0 : n.getArguments().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(MethodDeclaration n, Void arg) {
        return (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.isDefault() ? 1 : 0) * 31 + (n.getParameters() == null ? 0 : n.getParameters().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getTypeParameters() == null ? 0 : n.getTypeParameters().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getThrownExceptions() == null ? 0 : n.getThrownExceptions().hashCode());
    }

    public Integer visit(MethodReferenceExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getScope() == null ? 0 : n.getScope().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode()) * 31 + (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode());
    }

    public Integer visit(Name n, Void arg) {
        return (n.getQualifier() == null ? 0 : n.getQualifier().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(NameExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(NodeList n, Void arg) {
        return (n.getParentNode() == null ? 0 : n.getParentNode().hashCode());
    }

    public Integer visit(NormalAnnotationExpr n, Void arg) {
        return (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getPairs() == null ? 0 : n.getPairs().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(NullLiteralExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(ObjectCreationExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getScope() == null ? 0 : n.getScope().hashCode()) * 31 + (n.getAnonymousClassBody() == null ? 0 : n.getAnonymousClassBody().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getTypeArguments() == null ? 0 : n.getTypeArguments().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getArguments() == null ? 0 : n.getArguments().hashCode());
    }

    public Integer visit(PackageDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(Parameter n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.isVarArgs() ? 1 : 0) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(PrimitiveType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(ReturnStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SimpleName n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SingleMemberAnnotationExpr n, Void arg) {
        return (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getMemberValue() == null ? 0 : n.getMemberValue().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SingleStaticImportDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getStaticMember() == null ? 0 : n.getStaticMember().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SingleTypeImportDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode());
    }

    public Integer visit(StaticImportOnDemandDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode());
    }

    public Integer visit(StringLiteralExpr n, Void arg) {
        return (n.getValue() == null ? 0 : n.getValue().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SuperExpr n, Void arg) {
        return (n.getClassExpr() == null ? 0 : n.getClassExpr().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(SwitchEntryStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getStatements() == null ? 0 : n.getStatements().hashCode()) * 31 + (n.getLabel() == null ? 0 : n.getLabel().hashCode());
    }

    public Integer visit(SwitchStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getSelector() == null ? 0 : n.getSelector().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getEntries() == null ? 0 : n.getEntries().hashCode());
    }

    public Integer visit(SynchronizedStmt n, Void arg) {
        return (n.getBlock() == null ? 0 : n.getBlock().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode());
    }

    public Integer visit(ThisExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getClassExpr() == null ? 0 : n.getClassExpr().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(ThrowStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(TryStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getCatchClauses() == null ? 0 : n.getCatchClauses().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getTryBlock() == null ? 0 : n.getTryBlock().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getFinallyBlock() == null ? 0 : n.getFinallyBlock().hashCode()) * 31 + (n.getResources() == null ? 0 : n.getResources().hashCode());
    }

    public Integer visit(TypeDeclarationStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getTypeDeclaration() == null ? 0 : n.getTypeDeclaration().hashCode());
    }

    public Integer visit(TypeExpr n, Void arg) {
        return (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode());
    }

    public Integer visit(TypeImportOnDemandDeclaration n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode());
    }

    public Integer visit(TypeParameter n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getTypeBound() == null ? 0 : n.getTypeBound().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(UnaryExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getOperator() == null ? 0 : n.getOperator().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getExpression() == null ? 0 : n.getExpression().hashCode());
    }

    public Integer visit(UnionType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getElements() == null ? 0 : n.getElements().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(UnknownType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(VariableDeclarationExpr n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getModifiers() == null ? 0 : n.getModifiers().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getVariables() == null ? 0 : n.getVariables().hashCode());
    }

    public Integer visit(VariableDeclarator n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getName() == null ? 0 : n.getName().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getType() == null ? 0 : n.getType().hashCode()) * 31 + (n.getInitializer() == null ? 0 : n.getInitializer().hashCode());
    }

    public Integer visit(VoidType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }

    public Integer visit(WhileStmt n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getCondition() == null ? 0 : n.getCondition().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getBody() == null ? 0 : n.getBody().hashCode());
    }

    public Integer visit(WildcardType n, Void arg) {
        return (n.getOrphanComments() == null ? 0 : n.getOrphanComments().hashCode()) * 31 + (n.getExtendedTypes() == null ? 0 : n.getExtendedTypes().hashCode()) * 31 + (n.getComment() == null ? 0 : n.getComment().hashCode()) * 31 + (n.getSuperTypes() == null ? 0 : n.getSuperTypes().hashCode()) * 31 + (n.getParentNode() == null ? 0 : n.getParentNode().hashCode()) * 31 + (n.getRange() == null ? 0 : n.getRange().hashCode()) * 31 + (n.getChildNodes() == null ? 0 : n.getChildNodes().hashCode()) * 31 + (n.getAnnotations() == null ? 0 : n.getAnnotations().hashCode());
    }
}

