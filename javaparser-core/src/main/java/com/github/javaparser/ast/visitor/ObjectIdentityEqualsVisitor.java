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
 * A visitor that calculates deep node equality by comparing all properties and child nodes of the node.
 *
 * @author Julio Vilmar Gesser
 */
public class ObjectIdentityEqualsVisitor implements GenericVisitor<Boolean, Visitable> {

    private static final ObjectIdentityEqualsVisitor SINGLETON = new ObjectIdentityEqualsVisitor();

    public static boolean equals(final Node n, final Node n2) {
        return n.accept(SINGLETON, n2);
    }

    @Override
    public Boolean visit(final CompilationUnit n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final PackageDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final TypeParameter n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final LineComment n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final BlockComment n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ClassOrInterfaceDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final EnumDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final EnumConstantDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final AnnotationDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final AnnotationMemberDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final FieldDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final VariableDeclarator n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ConstructorDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final MethodDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final Parameter n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final InitializerDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final JavadocComment n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ClassOrInterfaceType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final PrimitiveType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ArrayType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ArrayCreationLevel n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final IntersectionType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final UnionType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final VoidType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final WildcardType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final UnknownType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ArrayAccessExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ArrayCreationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ArrayInitializerExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final AssignExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final BinaryExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final CastExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ClassExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ConditionalExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final EnclosedExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final FieldAccessExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final InstanceOfExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final StringLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final IntegerLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final LongLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final CharLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final DoubleLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final BooleanLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final NullLiteralExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final MethodCallExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final NameExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ObjectCreationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final Name n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SimpleName n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ThisExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SuperExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final UnaryExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final VariableDeclarationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final MarkerAnnotationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SingleMemberAnnotationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final NormalAnnotationExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final MemberValuePair n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ExplicitConstructorInvocationStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final LocalClassDeclarationStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final AssertStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final BlockStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final LabeledStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final EmptyStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ExpressionStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SwitchStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SwitchEntry n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final BreakStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ReturnStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final IfStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final WhileStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ContinueStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final DoStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ForEachStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ForStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ThrowStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SynchronizedStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final TryStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final CatchClause n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final LambdaExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final MethodReferenceExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final TypeExpr n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ImportDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(NodeList n, Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ModuleDeclaration n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ModuleRequiresDirective n, final Visitable arg) {
        return n == arg;
    }

    @Override()
    public Boolean visit(final ModuleExportsDirective n, final Visitable arg) {
        return n == arg;
    }

    @Override()
    public Boolean visit(final ModuleProvidesDirective n, final Visitable arg) {
        return n == arg;
    }

    @Override()
    public Boolean visit(final ModuleUsesDirective n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ModuleOpensDirective n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final UnparsableStmt n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final ReceiverParameter n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final VarType n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final Modifier n, final Visitable arg) {
        return n == arg;
    }

    @Override
    public Boolean visit(final SwitchExpr n, final Visitable arg) {
        return n == arg;
    }
}
