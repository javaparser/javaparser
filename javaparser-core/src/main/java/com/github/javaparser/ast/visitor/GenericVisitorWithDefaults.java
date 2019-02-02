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
 * A visitor that has a return value (R), and has default methods that are used when a specific visit method is not
 * overridden.
 */
public abstract class GenericVisitorWithDefaults<R, A> implements GenericVisitor<R, A> {

    /**
     * This will be called by every node visit method that is not overridden.
     */
    public R defaultAction(Node n, A arg) {
        return null;
    }

    /**
     * This will be called by the NodeList visit method when it is not overridden.
     */
    public R defaultAction(NodeList n, A arg) {
        return null;
    }

    @Override
    public R visit(final AnnotationDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final AnnotationMemberDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ArrayAccessExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ArrayCreationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ArrayInitializerExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final AssertStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final AssignExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final BinaryExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final BlockStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final BooleanLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final BreakStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final CastExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final CatchClause n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final CharLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ClassExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ClassOrInterfaceDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ClassOrInterfaceType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final CompilationUnit n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ConditionalExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ConstructorDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ContinueStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final DoStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final DoubleLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final EmptyStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final EnclosedExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final EnumConstantDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final EnumDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ExpressionStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final FieldAccessExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final FieldDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ForEachStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ForStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final IfStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final InitializerDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final InstanceOfExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final IntegerLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final JavadocComment n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final LabeledStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final LongLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final MarkerAnnotationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final MemberValuePair n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final MethodCallExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final MethodDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final NameExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final NormalAnnotationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final NullLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ObjectCreationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final PackageDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final Parameter n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final PrimitiveType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final Name n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SimpleName n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ArrayType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ArrayCreationLevel n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final IntersectionType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final UnionType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ReturnStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SingleMemberAnnotationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final StringLiteralExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SuperExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SwitchEntry n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SwitchStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SynchronizedStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ThisExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ThrowStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final TryStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final LocalClassDeclarationStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final TypeParameter n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final UnaryExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final UnknownType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final VariableDeclarationExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final VariableDeclarator n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final VoidType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final WhileStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final WildcardType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final LambdaExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final MethodReferenceExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final TypeExpr n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ImportDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final BlockComment n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final LineComment n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(NodeList n, A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ModuleDeclaration n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ModuleRequiresDirective n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override()
    public R visit(final ModuleExportsDirective n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override()
    public R visit(final ModuleProvidesDirective n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override()
    public R visit(final ModuleUsesDirective n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ModuleOpensDirective n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final UnparsableStmt n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final ReceiverParameter n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final VarType n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final Modifier n, final A arg) {
        return defaultAction(n, arg);
    }

    @Override
    public R visit(final SwitchExpr n, final A arg) {
        return defaultAction(n, arg);
    }
}
