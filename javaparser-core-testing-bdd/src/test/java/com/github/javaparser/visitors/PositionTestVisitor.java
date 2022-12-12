/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.visitors;

import com.github.javaparser.Position;
import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
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
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

public class PositionTestVisitor extends VoidVisitorAdapter<Object> {

    private int numberOfNodesVisited;

    @Override
    public void visit(final AnnotationDeclaration n, final Object arg) {
        doTest(n);
        doTest(n.getName());
        super.visit(n, arg);
    }

    @Override
    public void visit(final AnnotationMemberDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ArrayAccessExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ArrayCreationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ArrayInitializerExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final AssertStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final AssignExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final BinaryExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final BlockComment n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final BlockStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final BooleanLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final BreakStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final CastExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final CatchClause n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(LambdaExpr n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(MethodReferenceExpr n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(TypeExpr n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final CharLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ClassExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final Object arg) {
        doTest(n);
        doTest(n.getName());
        super.visit(n, arg);
    }

    @Override
    public void visit(final ClassOrInterfaceType n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final CompilationUnit n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ConditionalExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ConstructorDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ContinueStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final DoStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final DoubleLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final EmptyStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final EnclosedExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final EnumConstantDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final EnumDeclaration n, final Object arg) {
        doTest(n);
        doTest(n.getName());
        super.visit(n, arg);
    }

    @Override
    public void visit(final ExplicitConstructorInvocationStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ExpressionStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final FieldAccessExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final FieldDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ForEachStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ForStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final IfStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final InitializerDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final InstanceOfExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final IntegerLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final JavadocComment n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final LabeledStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final LineComment n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final LongLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final MarkerAnnotationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final MemberValuePair n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final MethodCallExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final MethodDeclaration n, final Object arg) {
        doTest(n);
        doTest(n.getName());
        super.visit(n, arg);
    }

    @Override
    public void visit(final NameExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final NormalAnnotationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final NullLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ObjectCreationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final PackageDeclaration n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final Parameter n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final PrimitiveType n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final Name n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(SimpleName n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(ArrayType n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(ArrayCreationLevel n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final IntersectionType n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(UnionType n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ReturnStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final SingleMemberAnnotationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final StringLiteralExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final SuperExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final SwitchEntry n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final SwitchStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final SynchronizedStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ThisExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final ThrowStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final TryStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final LocalClassDeclarationStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final LocalRecordDeclarationStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final TypeParameter n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final UnaryExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final VariableDeclarationExpr n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final VariableDeclarator n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final VoidType n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final WhileStmt n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(final WildcardType n, final Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    @Override
    public void visit(UnknownType n, Object arg) {
        doTest(n);
        super.visit(n, arg);
    }

    private void doTest(final Node node) {
        Position begin = node.getRange().get().begin;
        Position end = node.getRange().get().end;
        assertThat(begin.line, is(greaterThanOrEqualTo(0)));
        assertThat(begin.column, is(greaterThanOrEqualTo(0)));
        assertThat(end.line, is(greaterThanOrEqualTo(0)));
        assertThat(end.column, is(greaterThanOrEqualTo(0)));

        if (begin.line == end.line) {
            assertThat(begin.column, is(lessThanOrEqualTo(end.column)));
        } else {
            assertThat(begin.line, is(lessThanOrEqualTo(end.line)));
        }
        numberOfNodesVisited++;
    }

    public int getNumberOfNodesVisited() {
        return numberOfNodesVisited;
    }
}
