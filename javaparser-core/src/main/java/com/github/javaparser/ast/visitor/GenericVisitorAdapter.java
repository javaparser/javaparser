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
 * A visitor that has a return value (R), and has a default implementation for all its visit
 * methods that visits their children in an unspecified order, and the first visit method
 * that returns a value will stop the visitation and be the end result.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class GenericVisitorAdapter<R, A> implements GenericVisitor<R, A> {

    @Override
    public R visit(AnnotationDeclaration n, A arg) {
        R result;
        {
            result = n.getMembers().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(AnnotationMemberDeclaration n, A arg) {
        R result;
        if (n.getDefaultValue().isPresent()) {
            result = n.getDefaultValue().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ArrayAccessExpr n, A arg) {
        R result;
        {
            result = n.getIndex().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ArrayCreationExpr n, A arg) {
        R result;
        {
            result = n.getElementType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getInitializer().isPresent()) {
            result = n.getInitializer().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getLevels().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ArrayInitializerExpr n, A arg) {
        R result;
        {
            result = n.getValues().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(AssertStmt n, A arg) {
        R result;
        {
            result = n.getCheck().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getMessage().isPresent()) {
            result = n.getMessage().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(AssignExpr n, A arg) {
        R result;
        {
            result = n.getTarget().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getValue().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(BinaryExpr n, A arg) {
        R result;
        {
            result = n.getLeft().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getRight().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(BlockStmt n, A arg) {
        R result;
        {
            result = n.getStatements().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(BooleanLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(BreakStmt n, A arg) {
        R result;
        if (n.getLabel().isPresent()) {
            result = n.getLabel().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(CastExpr n, A arg) {
        R result;
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(CatchClause n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getParameter().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(CharLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ClassExpr n, A arg) {
        R result;
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ClassOrInterfaceDeclaration n, A arg) {
        R result;
        {
            result = n.getExtendedTypes().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getImplementedTypes().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getTypeParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getMembers().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ClassOrInterfaceType n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getScope().isPresent()) {
            result = n.getScope().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(CompilationUnit n, A arg) {
        R result;
        {
            result = n.getImports().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getModule().isPresent()) {
            result = n.getModule().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getPackageDeclaration().isPresent()) {
            result = n.getPackageDeclaration().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getTypes().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ConditionalExpr n, A arg) {
        R result;
        {
            result = n.getCondition().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getElseExpr().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getThenExpr().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ConstructorDeclaration n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getThrownExceptions().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getTypeParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ContinueStmt n, A arg) {
        R result;
        if (n.getLabel().isPresent()) {
            result = n.getLabel().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(DoStmt n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getCondition().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(DoubleLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(EmptyMemberDeclaration n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(EmptyStmt n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(EnclosedExpr n, A arg) {
        R result;
        if (n.getInner().isPresent()) {
            result = n.getInner().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(EnumConstantDeclaration n, A arg) {
        R result;
        {
            result = n.getArguments().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getClassBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(EnumDeclaration n, A arg) {
        R result;
        {
            result = n.getEntries().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getImplementedTypes().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getMembers().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ExplicitConstructorInvocationStmt n, A arg) {
        R result;
        {
            result = n.getArguments().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getExpression().isPresent()) {
            result = n.getExpression().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ExpressionStmt n, A arg) {
        R result;
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(FieldAccessExpr n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getScope().isPresent()) {
            result = n.getScope().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(FieldDeclaration n, A arg) {
        R result;
        {
            result = n.getVariables().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ForeachStmt n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getIterable().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getVariable().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ForStmt n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getCompare().isPresent()) {
            result = n.getCompare().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getInitialization().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getUpdate().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(IfStmt n, A arg) {
        R result;
        {
            result = n.getCondition().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getElseStmt().isPresent()) {
            result = n.getElseStmt().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getThenStmt().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(InitializerDeclaration n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(InstanceOfExpr n, A arg) {
        R result;
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(IntegerLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(JavadocComment n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(LabeledStmt n, A arg) {
        R result;
        {
            result = n.getLabel().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getStatement().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(LongLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(MarkerAnnotationExpr n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(MemberValuePair n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getValue().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(MethodCallExpr n, A arg) {
        R result;
        {
            result = n.getArguments().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getScope().isPresent()) {
            result = n.getScope().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(MethodDeclaration n, A arg) {
        R result;
        if (n.getBody().isPresent()) {
            result = n.getBody().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getThrownExceptions().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getTypeParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(NameExpr n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(NormalAnnotationExpr n, A arg) {
        R result;
        {
            result = n.getPairs().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(NullLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ObjectCreationExpr n, A arg) {
        R result;
        if (n.getAnonymousClassBody().isPresent()) {
            result = n.getAnonymousClassBody().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getArguments().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getScope().isPresent()) {
            result = n.getScope().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(PackageDeclaration n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(Parameter n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getVarArgsAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(PrimitiveType n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(Name n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getQualifier().isPresent()) {
            result = n.getQualifier().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SimpleName n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ArrayType n, A arg) {
        R result;
        {
            result = n.getComponentType().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ArrayCreationLevel n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getDimension().isPresent()) {
            result = n.getDimension().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(IntersectionType n, A arg) {
        R result;
        {
            result = n.getElements().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(UnionType n, A arg) {
        R result;
        {
            result = n.getElements().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ReturnStmt n, A arg) {
        R result;
        if (n.getExpression().isPresent()) {
            result = n.getExpression().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SingleMemberAnnotationExpr n, A arg) {
        R result;
        {
            result = n.getMemberValue().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(StringLiteralExpr n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SuperExpr n, A arg) {
        R result;
        if (n.getClassExpr().isPresent()) {
            result = n.getClassExpr().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SwitchEntryStmt n, A arg) {
        R result;
        if (n.getLabel().isPresent()) {
            result = n.getLabel().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getStatements().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SwitchStmt n, A arg) {
        R result;
        {
            result = n.getEntries().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getSelector().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(SynchronizedStmt n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ThisExpr n, A arg) {
        R result;
        if (n.getClassExpr().isPresent()) {
            result = n.getClassExpr().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ThrowStmt n, A arg) {
        R result;
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(TryStmt n, A arg) {
        R result;
        {
            result = n.getCatchClauses().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getFinallyBlock().isPresent()) {
            result = n.getFinallyBlock().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getResources().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTryBlock().isPresent()) {
            result = n.getTryBlock().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(LocalClassDeclarationStmt n, A arg) {
        R result;
        {
            result = n.getClassDeclaration().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(TypeParameter n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getTypeBound().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(UnaryExpr n, A arg) {
        R result;
        {
            result = n.getExpression().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(UnknownType n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(VariableDeclarationExpr n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getVariables().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(VariableDeclarator n, A arg) {
        R result;
        if (n.getInitializer().isPresent()) {
            result = n.getInitializer().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(VoidType n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(WhileStmt n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getCondition().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(WildcardType n, A arg) {
        R result;
        if (n.getExtendedType().isPresent()) {
            result = n.getExtendedType().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getSuperType().isPresent()) {
            result = n.getSuperType().get().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(LambdaExpr n, A arg) {
        R result;
        {
            result = n.getBody().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getParameters().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(MethodReferenceExpr n, A arg) {
        R result;
        {
            result = n.getScope().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getTypeArguments().isPresent()) {
            result = n.getTypeArguments().get().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(TypeExpr n, A arg) {
        R result;
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ImportDeclaration n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(BlockComment n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(LineComment n, A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(NodeList n, A arg) {
        for (final Object v : n) {
            R result = ((Node) v).accept(this, arg);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    @Override
    public R visit(ModuleDeclaration n, A arg) {
        R result;
        {
            result = n.getAnnotations().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getModuleStmts().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ModuleRequiresStmt n, A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override()
    public R visit(ModuleExportsStmt n, A arg) {
        R result;
        {
            result = n.getModuleNames().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override()
    public R visit(ModuleProvidesStmt n, A arg) {
        R result;
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getWithTypes().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override()
    public R visit(ModuleUsesStmt n, A arg) {
        R result;
        {
            result = n.getType().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(ModuleOpensStmt n, A arg) {
        R result;
        {
            result = n.getModuleNames().accept(this, arg);
            if (result != null)
                return result;
        }
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }
}

