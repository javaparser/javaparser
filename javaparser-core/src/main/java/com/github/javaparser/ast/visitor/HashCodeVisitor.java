/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

/**
 * A visitor that calculates a deep hash code for a node by using the hash codes of all its properties,
 * and the hash codes of all its child nodes (by visiting those too.)
 */
public class HashCodeVisitor implements GenericVisitor<Integer, Void> {

    private static final HashCodeVisitor SINGLETON = new HashCodeVisitor();

    private HashCodeVisitor() {
    // hide constructor
    }

    public static int hashCode(final Node node) {
        return node.accept(SINGLETON, null);
    }

    public Integer visit(AnnotationDeclaration n, Void arg) {
        return (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(AnnotationMemberDeclaration n, Void arg) {
        return (n.getDefaultValue().isPresent() ? n.getDefaultValue().get().accept(this, arg) : 0) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ArrayAccessExpr n, Void arg) {
        return (n.getIndex().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ArrayCreationExpr n, Void arg) {
        return (n.getElementType().accept(this, arg)) * 31 + (n.getInitializer().isPresent() ? n.getInitializer().get().accept(this, arg) : 0) * 31 + (n.getLevels().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ArrayCreationLevel n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getDimension().isPresent() ? n.getDimension().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ArrayInitializerExpr n, Void arg) {
        return (n.getValues().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ArrayType n, Void arg) {
        return (n.getComponentType().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(AssertStmt n, Void arg) {
        return (n.getCheck().accept(this, arg)) * 31 + (n.getMessage().isPresent() ? n.getMessage().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(AssignExpr n, Void arg) {
        return (n.getOperator().hashCode()) * 31 + (n.getTarget().accept(this, arg)) * 31 + (n.getValue().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(BinaryExpr n, Void arg) {
        return (n.getLeft().accept(this, arg)) * 31 + (n.getOperator().hashCode()) * 31 + (n.getRight().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(BlockComment n, Void arg) {
        return (n.getContent().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(BlockStmt n, Void arg) {
        return (n.getStatements().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(BooleanLiteralExpr n, Void arg) {
        return (n.getValue() ? 1 : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(BreakStmt n, Void arg) {
        return (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(CastExpr n, Void arg) {
        return (n.getExpression().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(CatchClause n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getParameter().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(CharLiteralExpr n, Void arg) {
        return (n.getValue().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ClassExpr n, Void arg) {
        return (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ClassOrInterfaceDeclaration n, Void arg) {
        return (n.getExtendedTypes().accept(this, arg)) * 31 + (n.getImplementedTypes().accept(this, arg)) * 31 + (n.isInterface() ? 1 : 0) * 31 + (n.getTypeParameters().accept(this, arg)) * 31 + (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ClassOrInterfaceType n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(CompilationUnit n, Void arg) {
        return (n.getImports().accept(this, arg)) * 31 + (n.getModule().isPresent() ? n.getModule().get().accept(this, arg) : 0) * 31 + (n.getPackageDeclaration().isPresent() ? n.getPackageDeclaration().get().accept(this, arg) : 0) * 31 + (n.getTypes().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ConditionalExpr n, Void arg) {
        return (n.getCondition().accept(this, arg)) * 31 + (n.getElseExpr().accept(this, arg)) * 31 + (n.getThenExpr().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ConstructorDeclaration n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getParameters().accept(this, arg)) * 31 + (n.getThrownExceptions().accept(this, arg)) * 31 + (n.getTypeParameters().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ContinueStmt n, Void arg) {
        return (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(DoStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(DoubleLiteralExpr n, Void arg) {
        return (n.getValue().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(EmptyMemberDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(EmptyStmt n, Void arg) {
        return (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(EnclosedExpr n, Void arg) {
        return (n.getInner().isPresent() ? n.getInner().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(EnumConstantDeclaration n, Void arg) {
        return (n.getArguments().accept(this, arg)) * 31 + (n.getClassBody().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(EnumDeclaration n, Void arg) {
        return (n.getEntries().accept(this, arg)) * 31 + (n.getImplementedTypes().accept(this, arg)) * 31 + (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return (n.getArguments().accept(this, arg)) * 31 + (n.getExpression().isPresent() ? n.getExpression().get().accept(this, arg) : 0) * 31 + (n.isThis() ? 1 : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ExpressionStmt n, Void arg) {
        return (n.getExpression().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(FieldAccessExpr n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(FieldDeclaration n, Void arg) {
        return (n.getModifiers().hashCode()) * 31 + (n.getVariables().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ForStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getCompare().isPresent() ? n.getCompare().get().accept(this, arg) : 0) * 31 + (n.getInitialization().accept(this, arg)) * 31 + (n.getUpdate().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ForeachStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getIterable().accept(this, arg)) * 31 + (n.getVariable().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(IfStmt n, Void arg) {
        return (n.getCondition().accept(this, arg)) * 31 + (n.getElseStmt().isPresent() ? n.getElseStmt().get().accept(this, arg) : 0) * 31 + (n.getThenStmt().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ImportDeclaration n, Void arg) {
        return (n.isAsterisk() ? 1 : 0) * 31 + (n.isStatic() ? 1 : 0) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(InitializerDeclaration n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.isStatic() ? 1 : 0) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(InstanceOfExpr n, Void arg) {
        return (n.getExpression().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(IntegerLiteralExpr n, Void arg) {
        return (n.getValue().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(IntersectionType n, Void arg) {
        return (n.getElements().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(JavadocComment n, Void arg) {
        return (n.getContent().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(LabeledStmt n, Void arg) {
        return (n.getLabel().accept(this, arg)) * 31 + (n.getStatement().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(LambdaExpr n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.isEnclosingParameters() ? 1 : 0) * 31 + (n.getParameters().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(LineComment n, Void arg) {
        return (n.getContent().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(LocalClassDeclarationStmt n, Void arg) {
        return (n.getClassDeclaration().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(LongLiteralExpr n, Void arg) {
        return (n.getValue().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(MarkerAnnotationExpr n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(MemberValuePair n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getValue().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(MethodCallExpr n, Void arg) {
        return (n.getArguments().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(MethodDeclaration n, Void arg) {
        return (n.getBody().isPresent() ? n.getBody().get().accept(this, arg) : 0) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getParameters().accept(this, arg)) * 31 + (n.getThrownExceptions().accept(this, arg)) * 31 + (n.getTypeParameters().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(MethodReferenceExpr n, Void arg) {
        return (n.getIdentifier().hashCode()) * 31 + (n.getScope().accept(this, arg)) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(NameExpr n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(Name n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getIdentifier().hashCode()) * 31 + (n.getQualifier().isPresent() ? n.getQualifier().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(NodeList n, Void arg) {
        int result = 0;
        for (Object node : n) {
            result += 31 * ((Visitable) node).accept(this, arg);
        }
        return result;
    }

    public Integer visit(NormalAnnotationExpr n, Void arg) {
        return (n.getPairs().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(NullLiteralExpr n, Void arg) {
        return (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ObjectCreationExpr n, Void arg) {
        return (n.getAnonymousClassBody().isPresent() ? n.getAnonymousClassBody().get().accept(this, arg) : 0) * 31 + (n.getArguments().accept(this, arg)) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(PackageDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(Parameter n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.isVarArgs() ? 1 : 0) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getVarArgsAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(PrimitiveType n, Void arg) {
        return (n.getType().hashCode()) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ReturnStmt n, Void arg) {
        return (n.getExpression().isPresent() ? n.getExpression().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SimpleName n, Void arg) {
        return (n.getIdentifier().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SingleMemberAnnotationExpr n, Void arg) {
        return (n.getMemberValue().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(StringLiteralExpr n, Void arg) {
        return (n.getValue().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SuperExpr n, Void arg) {
        return (n.getClassExpr().isPresent() ? n.getClassExpr().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SwitchEntryStmt n, Void arg) {
        return (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getStatements().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SwitchStmt n, Void arg) {
        return (n.getEntries().accept(this, arg)) * 31 + (n.getSelector().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(SynchronizedStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ThisExpr n, Void arg) {
        return (n.getClassExpr().isPresent() ? n.getClassExpr().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ThrowStmt n, Void arg) {
        return (n.getExpression().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(TryStmt n, Void arg) {
        return (n.getCatchClauses().accept(this, arg)) * 31 + (n.getFinallyBlock().isPresent() ? n.getFinallyBlock().get().accept(this, arg) : 0) * 31 + (n.getResources().accept(this, arg)) * 31 + (n.getTryBlock().isPresent() ? n.getTryBlock().get().accept(this, arg) : 0) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(TypeExpr n, Void arg) {
        return (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(TypeParameter n, Void arg) {
        return (n.getName().accept(this, arg)) * 31 + (n.getTypeBound().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(UnaryExpr n, Void arg) {
        return (n.getExpression().accept(this, arg)) * 31 + (n.getOperator().hashCode()) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(UnionType n, Void arg) {
        return (n.getElements().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(UnknownType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(VariableDeclarationExpr n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getVariables().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(VariableDeclarator n, Void arg) {
        return (n.getInitializer().isPresent() ? n.getInitializer().get().accept(this, arg) : 0) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(VoidType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(WhileStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(WildcardType n, Void arg) {
        return (n.getExtendedType().isPresent() ? n.getExtendedType().get().accept(this, arg) : 0) * 31 + (n.getSuperType().isPresent() ? n.getSuperType().get().accept(this, arg) : 0) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ModuleDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.isOpen() ? 1 : 0) * 31 + (n.getModuleStmts().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    public Integer visit(ModuleRequiresStmt n, Void arg) {
        return (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    @Override()
    public Integer visit(ModuleExportsStmt n, Void arg) {
        return (n.getModuleNames().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    @Override()
    public Integer visit(ModuleProvidesStmt n, Void arg) {
        return (n.getType().accept(this, arg)) * 31 + (n.getWithTypes().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    @Override()
    public Integer visit(ModuleUsesStmt n, Void arg) {
        return (n.getType().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }

    @Override
    public Integer visit(ModuleOpensStmt n, Void arg) {
        return (n.getModuleNames().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getComment().isPresent() ? n.getComment().get().accept(this, arg) : 0);
    }
}
