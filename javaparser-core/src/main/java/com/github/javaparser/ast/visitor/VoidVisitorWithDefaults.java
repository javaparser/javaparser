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
 * A visitor that returns nothing, and has default methods that are used when a specific visit method is not
 * overridden.
 */
public abstract class VoidVisitorWithDefaults<A> implements VoidVisitor<A> {

    /**
     * This will be called by every node visit method that is not overridden.
     */
    public void defaultAction(Node n, A arg) {
    }

    /**
     * This will be called by the NodeList visit method when it is not overridden.
     */
    public void defaultAction(NodeList n, A arg) {
    }

    @Override
    public void visit(final AnnotationDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final AnnotationMemberDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ArrayAccessExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ArrayCreationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ArrayInitializerExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final AssertStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final AssignExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final BinaryExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final BlockComment n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final BlockStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final BooleanLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final BreakStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final CastExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final CatchClause n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final CharLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ClassExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ClassOrInterfaceType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final CompilationUnit n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ConditionalExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ConstructorDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ContinueStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final DoStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final DoubleLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final EmptyStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final EnclosedExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final EnumConstantDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final EnumDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ExpressionStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final FieldAccessExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final FieldDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ForEachStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ForStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final IfStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final InitializerDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final InstanceOfExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final IntegerLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final JavadocComment n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final LabeledStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final LineComment n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final LongLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final MarkerAnnotationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final MemberValuePair n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final MethodCallExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final MethodDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final NameExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final NormalAnnotationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final NullLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ObjectCreationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final PackageDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final Parameter n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final PrimitiveType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final Name n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SimpleName n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ArrayType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ArrayCreationLevel n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final IntersectionType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final UnionType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ReturnStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SingleMemberAnnotationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final StringLiteralExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SuperExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SwitchEntry n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SwitchStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SynchronizedStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ThisExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ThrowStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final TryStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final LocalClassDeclarationStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final TypeParameter n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final UnaryExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final UnknownType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final VariableDeclarationExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final VariableDeclarator n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final VoidType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final WhileStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final WildcardType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final LambdaExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final MethodReferenceExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final TypeExpr n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(NodeList n, A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ImportDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    public void visit(final ModuleDeclaration n, final A arg) {
        defaultAction(n, arg);
    }

    public void visit(final ModuleRequiresDirective n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ModuleExportsDirective n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ModuleProvidesDirective n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ModuleUsesDirective n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ModuleOpensDirective n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final UnparsableStmt n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final ReceiverParameter n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final Modifier n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final VarType n, final A arg) {
        defaultAction(n, arg);
    }

    @Override
    public void visit(final SwitchExpr n, final A arg) {
        defaultAction(n, arg);
    }
}
