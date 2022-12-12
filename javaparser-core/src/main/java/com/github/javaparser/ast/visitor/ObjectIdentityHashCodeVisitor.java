/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.body.RecordDeclaration;
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
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleExportsDirective;
import com.github.javaparser.ast.modules.ModuleOpensDirective;
import com.github.javaparser.ast.modules.ModuleProvidesDirective;
import com.github.javaparser.ast.modules.ModuleRequiresDirective;
import com.github.javaparser.ast.modules.ModuleUsesDirective;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.LocalRecordDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.stmt.YieldStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;

/**
 * A visitor that calculates a deep hash code for a node by using the hash codes of all its properties,
 * and the hash codes of all its child nodes (by visiting those too.)
 */
public class ObjectIdentityHashCodeVisitor implements GenericVisitor<Integer, Void> {

    private static final ObjectIdentityHashCodeVisitor SINGLETON = new ObjectIdentityHashCodeVisitor();

    public static int hashCode(final Node node) {
        return node.accept(SINGLETON, null);
    }

    public Integer visit(final AnnotationDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AnnotationMemberDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayAccessExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayCreationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayCreationLevel n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayInitializerExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AssertStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AssignExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BinaryExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BlockComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BlockStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BooleanLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BreakStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CastExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CatchClause n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CharLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassOrInterfaceDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassOrInterfaceType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CompilationUnit n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ConditionalExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ConstructorDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ContinueStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final DoStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final DoubleLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EmptyStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnclosedExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnumConstantDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnumDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ExplicitConstructorInvocationStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ExpressionStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final FieldAccessExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final FieldDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ForStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ForEachStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IfStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ImportDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final InitializerDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final InstanceOfExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IntegerLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IntersectionType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final JavadocComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LabeledStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LambdaExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LineComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LocalClassDeclarationStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LocalRecordDeclarationStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LongLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MarkerAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MemberValuePair n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodCallExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodReferenceExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NameExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final Name n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(NodeList n, Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NormalAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NullLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ObjectCreationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final PackageDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final Parameter n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final PrimitiveType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ReturnStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SimpleName n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SingleMemberAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final StringLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SuperExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SwitchEntry n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SwitchStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SynchronizedStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ThisExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ThrowStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TryStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TypeExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TypeParameter n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnaryExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnionType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnknownType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VariableDeclarationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VariableDeclarator n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VoidType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final WhileStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final WildcardType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ModuleDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ModuleRequiresDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleExportsDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleProvidesDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleUsesDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final ModuleOpensDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final UnparsableStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final ReceiverParameter n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final VarType n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final Modifier n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final SwitchExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final YieldStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final TextBlockLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final PatternExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final RecordDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CompactConstructorDeclaration n, final Void arg) {
        return n.hashCode();
    }
}
