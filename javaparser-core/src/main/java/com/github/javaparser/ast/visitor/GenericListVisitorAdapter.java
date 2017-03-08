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

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EmptyMemberDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.ArrayList;

/**
 * A visitor that has a return value of ({@link List<R>}), and has a default implementation for all its visit
 * methods that visits their children in an unspecified order, and all visit methods
 * that returns a value be added to a flattened {@link List<R>}.
 *
 * @author Enno Boland
 */
public abstract class GenericListVisitorAdapter<R, A> implements GenericVisitor<List<R>, A> {

    public List<R> visit(AnnotationDeclaration n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getMembers().accept(this, arg);
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

    public List<R> visit(AnnotationMemberDeclaration n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getDefaultValue().isPresent()) {
            tmp = n.getDefaultValue().get().accept(this, arg);
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

    public List<R> visit(ArrayAccessExpr n, A arg) {
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

    public List<R> visit(ArrayCreationExpr n, A arg) {
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

    public List<R> visit(ArrayCreationLevel n, A arg) {
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

    public List<R> visit(ArrayInitializerExpr n, A arg) {
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

    public List<R> visit(ArrayType n, A arg) {
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

    public List<R> visit(AssertStmt n, A arg) {
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

    public List<R> visit(AssignExpr n, A arg) {
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

    public List<R> visit(BinaryExpr n, A arg) {
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

    public List<R> visit(BlockComment n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(BlockStmt n, A arg) {
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

    public List<R> visit(BooleanLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(BreakStmt n, A arg) {
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

    public List<R> visit(CastExpr n, A arg) {
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

    public List<R> visit(CatchClause n, A arg) {
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

    public List<R> visit(CharLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(ClassExpr n, A arg) {
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

    public List<R> visit(ClassOrInterfaceDeclaration n, A arg) {
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

    public List<R> visit(ClassOrInterfaceType n, A arg) {
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

    public List<R> visit(CompilationUnit n, A arg) {
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

    public List<R> visit(ConditionalExpr n, A arg) {
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

    public List<R> visit(ConstructorDeclaration n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getBody().accept(this, arg);
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

    public List<R> visit(ContinueStmt n, A arg) {
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

    public List<R> visit(DoStmt n, A arg) {
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

    public List<R> visit(DoubleLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(EmptyMemberDeclaration n, A arg) {
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

    public List<R> visit(EmptyStmt n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(EnclosedExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getInner().isPresent()) {
            tmp = n.getInner().get().accept(this, arg);
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

    public List<R> visit(EnumConstantDeclaration n, A arg) {
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

    public List<R> visit(EnumDeclaration n, A arg) {
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

    public List<R> visit(ExplicitConstructorInvocationStmt n, A arg) {
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

    public List<R> visit(ExpressionStmt n, A arg) {
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

    public List<R> visit(FieldAccessExpr n, A arg) {
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
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(FieldDeclaration n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
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

    public List<R> visit(ForStmt n, A arg) {
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

    public List<R> visit(ForeachStmt n, A arg) {
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

    public List<R> visit(IfStmt n, A arg) {
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

    public List<R> visit(ImportDeclaration n, A arg) {
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

    public List<R> visit(InitializerDeclaration n, A arg) {
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

    public List<R> visit(InstanceOfExpr n, A arg) {
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

    public List<R> visit(IntegerLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(IntersectionType n, A arg) {
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

    public List<R> visit(JavadocComment n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(LabeledStmt n, A arg) {
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

    public List<R> visit(LambdaExpr n, A arg) {
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

    public List<R> visit(LineComment n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(LocalClassDeclarationStmt n, A arg) {
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

    public List<R> visit(LongLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(MarkerAnnotationExpr n, A arg) {
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

    public List<R> visit(MemberValuePair n, A arg) {
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

    public List<R> visit(MethodCallExpr n, A arg) {
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

    public List<R> visit(MethodDeclaration n, A arg) {
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
            tmp = n.getName().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getParameters().accept(this, arg);
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

    public List<R> visit(MethodReferenceExpr n, A arg) {
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

    public List<R> visit(NameExpr n, A arg) {
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

    public List<R> visit(Name n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
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

    public List<R> visit(NormalAnnotationExpr n, A arg) {
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

    public List<R> visit(NullLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(ObjectCreationExpr n, A arg) {
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

    public List<R> visit(PackageDeclaration n, A arg) {
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

    public List<R> visit(Parameter n, A arg) {
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

    public List<R> visit(PrimitiveType n, A arg) {
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

    public List<R> visit(ReturnStmt n, A arg) {
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

    public List<R> visit(SimpleName n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(SingleMemberAnnotationExpr n, A arg) {
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

    public List<R> visit(StringLiteralExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getComment().isPresent()) {
            tmp = n.getComment().get().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        return result;
    }

    public List<R> visit(SuperExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getClassExpr().isPresent()) {
            tmp = n.getClassExpr().get().accept(this, arg);
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

    public List<R> visit(SwitchEntryStmt n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getLabel().isPresent()) {
            tmp = n.getLabel().get().accept(this, arg);
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

    public List<R> visit(SwitchStmt n, A arg) {
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

    public List<R> visit(SynchronizedStmt n, A arg) {
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

    public List<R> visit(ThisExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        if (n.getClassExpr().isPresent()) {
            tmp = n.getClassExpr().get().accept(this, arg);
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

    public List<R> visit(ThrowStmt n, A arg) {
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

    public List<R> visit(TryStmt n, A arg) {
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
        if (n.getTryBlock().isPresent()) {
            tmp = n.getTryBlock().get().accept(this, arg);
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

    public List<R> visit(TypeExpr n, A arg) {
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

    public List<R> visit(TypeParameter n, A arg) {
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

    public List<R> visit(UnaryExpr n, A arg) {
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

    public List<R> visit(UnionType n, A arg) {
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

    public List<R> visit(UnknownType n, A arg) {
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

    public List<R> visit(VariableDeclarationExpr n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
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

    public List<R> visit(VariableDeclarator n, A arg) {
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

    public List<R> visit(VoidType n, A arg) {
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

    public List<R> visit(WhileStmt n, A arg) {
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

    public List<R> visit(WildcardType n, A arg) {
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
    public List<R> visit(ModuleDeclaration n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getAnnotations().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getModuleStmts().accept(this, arg);
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
    public List<R> visit(ModuleExportsStmt n, A arg) {
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
    public List<R> visit(ModuleOpensStmt n, A arg) {
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
    public List<R> visit(ModuleProvidesStmt n, A arg) {
        List<R> result = new ArrayList<>();
        List<R> tmp;
        {
            tmp = n.getType().accept(this, arg);
            if (tmp != null)
                result.addAll(tmp);
        }
        {
            tmp = n.getWithTypes().accept(this, arg);
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
    public List<R> visit(ModuleRequiresStmt n, A arg) {
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
    public List<R> visit(ModuleUsesStmt n, A arg) {
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
}
