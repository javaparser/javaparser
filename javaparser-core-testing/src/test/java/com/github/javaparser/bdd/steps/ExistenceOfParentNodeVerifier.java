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

package com.github.javaparser.bdd.steps;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.assertThat;

/**
 * The <code>ExistenceOfParentNodeVerifier</code> verifies that each node of the compilation unit has a parent set.
 */
class ExistenceOfParentNodeVerifier {

    public void verify(CompilationUnit compilationUnit) throws AssertionError {
        new Verifier().visit(compilationUnit, null);
    }

    private static class Verifier extends VoidVisitorAdapter<Void> {
        private static void assertParentIsSet(HasParentNode<?> n) {
            assertThat(n + " has no parent set!", n.getParentNode().orElse(null), is(notNullValue()));
        }

        @Override
        public void visit(AnnotationDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(AnnotationMemberDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ArrayAccessExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ArrayCreationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ArrayInitializerExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(AssertStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(AssignExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(BinaryExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(BlockComment n, Void arg) {
            super.visit(n, arg);
        }

        @Override
        public void visit(BlockStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(BooleanLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(BreakStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(CastExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(CatchClause n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(CharLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ClassExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ClassOrInterfaceDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ClassOrInterfaceType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(CompilationUnit n, Void arg) {
            super.visit(n, arg);
        }

        @Override
        public void visit(ConditionalExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ConstructorDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ContinueStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(DoStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(DoubleLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(EmptyStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(EnclosedExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(EnumConstantDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(EnumDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ExplicitConstructorInvocationStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ExpressionStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(FieldAccessExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(FieldDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ForeachStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ForStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(IfStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(InitializerDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(InstanceOfExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(IntegerLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(JavadocComment n, Void arg) {
            super.visit(n, arg);
        }

        @Override
        public void visit(LabeledStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(LineComment n, Void arg) {
            super.visit(n, arg);
        }

        @Override
        public void visit(LambdaExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(LongLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MarkerAnnotationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MemberValuePair n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MethodCallExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MethodDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(MethodReferenceExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(NameExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(NormalAnnotationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(NullLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ObjectCreationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(PackageDeclaration n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(Parameter n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(PrimitiveType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(Name n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SimpleName n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ArrayType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ArrayCreationLevel n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(IntersectionType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(UnionType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ReturnStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SingleMemberAnnotationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(StringLiteralExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SuperExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SwitchEntryStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SwitchStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(SynchronizedStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ThisExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(ThrowStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(TryStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(LocalClassDeclarationStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(TypeExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(NodeList n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(TypeParameter n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(UnaryExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(UnknownType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(VariableDeclarationExpr n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(VariableDeclarator n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(VoidType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(WhileStmt n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }

        @Override
        public void visit(WildcardType n, Void arg) {
            assertParentIsSet(n);
            super.visit(n, arg);
        }
    }

}
