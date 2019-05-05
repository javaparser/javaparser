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
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * A visitor that has a return value of ({@link List List<R>}), and has a default implementation for all its visit
 * methods that visits their children in an unspecified order, and all visit methods
 * that returns a value be added to a flattened {@link List List<R>}.
 *
 * @author Enno Boland
 */
public abstract class GenericListVisitorAdapter<R, A> implements GenericVisitor<List<R>, A> {

    public List<R> visit(final AnnotationDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getMembers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final AnnotationMemberDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getDefaultValue().isPresent()) {
            tmp = n.getDefaultValue().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ArrayAccessExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getIndex().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ArrayCreationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getElementType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getInitializer().isPresent()) {
            tmp = n.getInitializer().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getLevels().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ArrayCreationLevel n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getDimension().isPresent()) {
            tmp = n.getDimension().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ArrayInitializerExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getValues().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ArrayType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getComponentType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final AssertStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getCheck().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getMessage().isPresent()) {
            tmp = n.getMessage().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final AssignExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getTarget().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getValue().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final BinaryExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getLeft().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getRight().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final BlockComment n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final BlockStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getStatements().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final BooleanLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final BreakStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getValue().isPresent()) {
            tmp = n.getValue().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final CastExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final CatchClause n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getParameter().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final CharLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ClassExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ClassOrInterfaceDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExtendedTypes().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getImplementedTypes().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTypeParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getMembers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ClassOrInterfaceType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getScope().isPresent()) {
            tmp = n.getScope().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final CompilationUnit n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getImports().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getModule().isPresent()) {
            tmp = n.getModule().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getPackageDeclaration().isPresent()) {
            tmp = n.getPackageDeclaration().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTypes().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ConditionalExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getCondition().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getElseExpr().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getThenExpr().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ConstructorDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getReceiverParameter().isPresent()) {
            tmp = n.getReceiverParameter().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getThrownExceptions().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTypeParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ContinueStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getLabel().isPresent()) {
            tmp = n.getLabel().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final DoStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getCondition().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final DoubleLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final EmptyStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final EnclosedExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getInner().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final EnumConstantDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getArguments().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getClassBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final EnumDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getEntries().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getImplementedTypes().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getMembers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getArguments().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getExpression().isPresent()) {
            tmp = n.getExpression().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ExpressionStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final FieldAccessExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getScope().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final FieldDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getVariables().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ForStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getCompare().isPresent()) {
            tmp = n.getCompare().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getInitialization().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getUpdate().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ForEachStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getIterable().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getVariable().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final IfStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getCondition().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getElseStmt().isPresent()) {
            tmp = n.getElseStmt().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getThenStmt().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ImportDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final InitializerDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final InstanceOfExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final IntegerLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final IntersectionType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getElements().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final JavadocComment n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final LabeledStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getLabel().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getStatement().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final LambdaExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final LineComment n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final LocalClassDeclarationStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getClassDeclaration().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final LongLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final MarkerAnnotationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final MemberValuePair n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getValue().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final MethodCallExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getArguments().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getScope().isPresent()) {
            tmp = n.getScope().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final MethodDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getBody().isPresent()) {
            tmp = n.getBody().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getReceiverParameter().isPresent()) {
            tmp = n.getReceiverParameter().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getThrownExceptions().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTypeParameters().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final MethodReferenceExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getScope().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final NameExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final Name n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getQualifier().isPresent()) {
            tmp = n.getQualifier().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final NormalAnnotationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getPairs().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final NullLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ObjectCreationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getAnonymousClassBody().isPresent()) {
            tmp = n.getAnonymousClassBody().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getArguments().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getScope().isPresent()) {
            tmp = n.getScope().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getTypeArguments().isPresent()) {
            tmp = n.getTypeArguments().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final PackageDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final Parameter n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getVarArgsAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final PrimitiveType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ReturnStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getExpression().isPresent()) {
            tmp = n.getExpression().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SimpleName n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SingleMemberAnnotationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getMemberValue().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final StringLiteralExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SuperExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getTypeName().isPresent()) {
            tmp = n.getTypeName().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SwitchEntry n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getLabels().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getStatements().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SwitchStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getEntries().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getSelector().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final SynchronizedStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ThisExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getTypeName().isPresent()) {
            tmp = n.getTypeName().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final ThrowStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final TryStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getCatchClauses().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getFinallyBlock().isPresent()) {
            tmp = n.getFinallyBlock().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getResources().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTryBlock().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final TypeExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final TypeParameter n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getTypeBound().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final UnaryExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getExpression().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final UnionType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getElements().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final UnknownType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final VariableDeclarationExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getVariables().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final VariableDeclarator n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getInitializer().isPresent()) {
            tmp = n.getInitializer().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final VoidType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final WhileStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getCondition().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(final WildcardType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getExtendedType().isPresent()) {
            tmp = n.getExtendedType().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getSuperType().isPresent()) {
            tmp = n.getSuperType().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(NodeList n, A arg) {
        return ((NodeList<? extends Node>) n).stream().filter(Objects::nonNull).flatMap(v -> v.accept(this, arg).stream()).collect(Collectors.toList());
    }

    @Override
    public List<R> visit(final ModuleDeclaration n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getDirectives().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ModuleExportsDirective n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getModuleNames().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ModuleOpensDirective n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getModuleNames().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ModuleProvidesDirective n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getWith().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ModuleRequiresDirective n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getModifiers().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ModuleUsesDirective n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final UnparsableStmt n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final ReceiverParameter n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final VarType n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final Modifier n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    @Override
    public List<R> visit(final SwitchExpr n, final A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getEntries().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getSelector().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }
}
