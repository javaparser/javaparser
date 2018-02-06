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
import javax.annotation.Generated;

/**
 * A visitor that has a return value (R), and has a default implementation for all its visit
 * methods that visits their children in an unspecified order, and the first visit method
 * that returns a value will stop the visitation and be the end result.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class GenericVisitorAdapter<R, A> implements GenericVisitor<R, A> {

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final AnnotationDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final AnnotationMemberDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ArrayAccessExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ArrayCreationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ArrayInitializerExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final AssertStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final AssignExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final BinaryExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final BlockStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final BooleanLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final BreakStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final CastExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final CatchClause n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final CharLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ClassExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ClassOrInterfaceDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ClassOrInterfaceType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final CompilationUnit n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ConditionalExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ConstructorDeclaration n, final A arg) {
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
        if (n.getReceiverParameter().isPresent()) {
            result = n.getReceiverParameter().get().accept(this, arg);
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ContinueStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final DoStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final DoubleLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final EmptyStmt n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final EnclosedExpr n, final A arg) {
        R result;
        {
            result = n.getInner().accept(this, arg);
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final EnumConstantDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final EnumDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ExplicitConstructorInvocationStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ExpressionStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final FieldAccessExpr n, final A arg) {
        R result;
        {
            result = n.getName().accept(this, arg);
            if (result != null)
                return result;
        }
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final FieldDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ForeachStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ForStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final IfStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final InitializerDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final InstanceOfExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final IntegerLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final JavadocComment n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final LabeledStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final LongLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final MarkerAnnotationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final MemberValuePair n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final MethodCallExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final MethodDeclaration n, final A arg) {
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
        if (n.getReceiverParameter().isPresent()) {
            result = n.getReceiverParameter().get().accept(this, arg);
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final NameExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final NormalAnnotationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final NullLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ObjectCreationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final PackageDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final Parameter n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final PrimitiveType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final Name n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SimpleName n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ArrayType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ArrayCreationLevel n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final IntersectionType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final UnionType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ReturnStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SingleMemberAnnotationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final StringLiteralExpr n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SuperExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SwitchEntryStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SwitchStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final SynchronizedStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ThisExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ThrowStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final TryStmt n, final A arg) {
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
        {
            result = n.getTryBlock().accept(this, arg);
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final LocalClassDeclarationStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final TypeParameter n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final UnaryExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final UnknownType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final VariableDeclarationExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final VariableDeclarator n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final VoidType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final WhileStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final WildcardType n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final LambdaExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final MethodReferenceExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final TypeExpr n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ImportDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final BlockComment n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final LineComment n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleDeclaration n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleRequiresStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleExportsStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleProvidesStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleUsesStmt n, final A arg) {
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
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ModuleOpensStmt n, final A arg) {
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

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final UnparsableStmt n, final A arg) {
        R result;
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorAdapterGenerator")
    public R visit(final ReceiverParameter n, final A arg) {
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
        if (n.getComment().isPresent()) {
            result = n.getComment().get().accept(this, arg);
            if (result != null)
                return result;
        }
        return null;
    }

    @Override
    public R visit(final VarType n, final A arg) {
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
}
