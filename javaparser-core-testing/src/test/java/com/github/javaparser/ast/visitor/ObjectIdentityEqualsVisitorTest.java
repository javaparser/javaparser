/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class ObjectIdentityEqualsVisitorTest {

    @Test
    void equals_GivenCompilationUnit() {
        Node nodeA = new CompilationUnit();
        Node nodeB = new CompilationUnit();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenPackageDeclaration() {
        Node nodeA = new PackageDeclaration();
        Node nodeB = new PackageDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenTypeParameter() {
        Node nodeA = new TypeParameter();
        Node nodeB = new TypeParameter();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLineComment() {
        Node nodeA = new LineComment();
        Node nodeB = new LineComment();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenBlockComment() {
        Node nodeA = new BlockComment();
        Node nodeB = new BlockComment();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenClassOrInterfaceDeclaration() {
        Node nodeA = new ClassOrInterfaceDeclaration();
        Node nodeB = new ClassOrInterfaceDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenEnumDeclaration() {
        Node nodeA = new EnumDeclaration();
        Node nodeB = new EnumDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenEnumConstantDeclaration() {
        Node nodeA = new EnumConstantDeclaration();
        Node nodeB = new EnumConstantDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenAnnotationDeclaration() {
        Node nodeA = new AnnotationDeclaration();
        Node nodeB = new AnnotationDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenAnnotationMemberDeclaration() {
        Node nodeA = new AnnotationMemberDeclaration();
        Node nodeB = new AnnotationMemberDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenFieldDeclaration() {
        Node nodeA = new FieldDeclaration();
        Node nodeB = new FieldDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenVariableDeclarator() {
        Node nodeA = new VariableDeclarator();
        Node nodeB = new VariableDeclarator();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenConstructorDeclaration() {
        Node nodeA = new ConstructorDeclaration();
        Node nodeB = new ConstructorDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenMethodDeclaration() {
        Node nodeA = new MethodDeclaration();
        Node nodeB = new MethodDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenParameter() {
        Node nodeA = new Parameter();
        Node nodeB = new Parameter();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenInitializerDeclaration() {
        Node nodeA = new InitializerDeclaration();
        Node nodeB = new InitializerDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenJavadocComment() {
        Node nodeA = new JavadocComment();
        Node nodeB = new JavadocComment();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenClassOrInterfaceType() {
        Node nodeA = new ClassOrInterfaceType();
        Node nodeB = new ClassOrInterfaceType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenPrimitiveType() {
        Node nodeA = new PrimitiveType();
        Node nodeB = new PrimitiveType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenArrayType() {
        Node nodeA = new ArrayType(new VoidType());
        Node nodeB = new ArrayType(new VoidType());

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenArrayCreationLevel() {
        Node nodeA = new ArrayCreationLevel();
        Node nodeB = new ArrayCreationLevel();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenIntersectionType() {
        Node nodeA = new IntersectionType(new NodeList<>());
        Node nodeB = new IntersectionType(new NodeList<>());

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenUnionType() {
        Node nodeA = new UnionType();
        Node nodeB = new UnionType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenVoidType() {
        Node nodeA = new VoidType();
        Node nodeB = new VoidType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenWildcardType() {
        Node nodeA = new WildcardType();
        Node nodeB = new WildcardType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenUnknownType() {
        Node nodeA = new UnknownType();
        Node nodeB = new UnknownType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenArrayAccessExpr() {
        Node nodeA = new ArrayAccessExpr();
        Node nodeB = new ArrayAccessExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenArrayCreationExpr() {
        Node nodeA = new ArrayCreationExpr();
        Node nodeB = new ArrayCreationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenArrayInitializerExpr() {
        Node nodeA = new ArrayInitializerExpr();
        Node nodeB = new ArrayInitializerExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenAssignExpr() {
        Node nodeA = new AssignExpr();
        Node nodeB = new AssignExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenBinaryExpr() {
        Node nodeA = new BinaryExpr();
        Node nodeB = new BinaryExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenCastExpr() {
        Node nodeA = new CastExpr();
        Node nodeB = new CastExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenClassExpr() {
        Node nodeA = new ClassExpr();
        Node nodeB = new ClassExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenConditionalExpr() {
        Node nodeA = new ConditionalExpr();
        Node nodeB = new ConditionalExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenEnclosedExpr() {
        Node nodeA = new EnclosedExpr();
        Node nodeB = new EnclosedExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenFieldAccessExpr() {
        Node nodeA = new FieldAccessExpr();
        Node nodeB = new FieldAccessExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenInstanceOfExpr() {
        Node nodeA = new InstanceOfExpr();
        Node nodeB = new InstanceOfExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenStringLiteralExpr() {
        Node nodeA = new StringLiteralExpr();
        Node nodeB = new StringLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenIntegerLiteralExpr() {
        Node nodeA = new IntegerLiteralExpr();
        Node nodeB = new IntegerLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLongLiteralExpr() {
        Node nodeA = new LongLiteralExpr();
        Node nodeB = new LongLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenCharLiteralExpr() {
        Node nodeA = new CharLiteralExpr();
        Node nodeB = new CharLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenDoubleLiteralExpr() {
        Node nodeA = new DoubleLiteralExpr();
        Node nodeB = new DoubleLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenBooleanLiteralExpr() {
        Node nodeA = new BooleanLiteralExpr();
        Node nodeB = new BooleanLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenNullLiteralExpr() {
        Node nodeA = new NullLiteralExpr();
        Node nodeB = new NullLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenMethodCallExpr() {
        Node nodeA = new MethodCallExpr();
        Node nodeB = new MethodCallExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenNameExpr() {
        Node nodeA = new NameExpr();
        Node nodeB = new NameExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenObjectCreationExpr() {
        Node nodeA = new ObjectCreationExpr();
        Node nodeB = new ObjectCreationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenName() {
        Node nodeA = new Name();
        Node nodeB = new Name();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSimpleName() {
        Node nodeA = new SimpleName();
        Node nodeB = new SimpleName();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenThisExpr() {
        Node nodeA = new ThisExpr();
        Node nodeB = new ThisExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSuperExpr() {
        Node nodeA = new SuperExpr();
        Node nodeB = new SuperExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenUnaryExpr() {
        Node nodeA = new UnaryExpr();
        Node nodeB = new UnaryExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenVariableDeclarationExpr() {
        Node nodeA = new VariableDeclarationExpr();
        Node nodeB = new VariableDeclarationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenMarkerAnnotationExpr() {
        Node nodeA = new MarkerAnnotationExpr();
        Node nodeB = new MarkerAnnotationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSingleMemberAnnotationExpr() {
        Node nodeA = new SingleMemberAnnotationExpr();
        Node nodeB = new SingleMemberAnnotationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenNormalAnnotationExpr() {
        Node nodeA = new NormalAnnotationExpr();
        Node nodeB = new NormalAnnotationExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenMemberValuePair() {
        Node nodeA = new MemberValuePair();
        Node nodeB = new MemberValuePair();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenExplicitConstructorInvocationStmt() {
        Node nodeA = new ExplicitConstructorInvocationStmt();
        Node nodeB = new ExplicitConstructorInvocationStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLocalClassDeclarationStmt() {
        Node nodeA = new LocalClassDeclarationStmt();
        Node nodeB = new LocalClassDeclarationStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLocalRecordDeclarationStmt() {
        Node nodeA = new LocalRecordDeclarationStmt();
        Node nodeB = new LocalRecordDeclarationStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenAssertStmt() {
        Node nodeA = new AssertStmt();
        Node nodeB = new AssertStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenBlockStmt() {
        Node nodeA = new BlockStmt();
        Node nodeB = new BlockStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLabeledStmt() {
        Node nodeA = new LabeledStmt();
        Node nodeB = new LabeledStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenEmptyStmt() {
        Node nodeA = new EmptyStmt();
        Node nodeB = new EmptyStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenExpressionStmt() {
        Node nodeA = new ExpressionStmt();
        Node nodeB = new ExpressionStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSwitchStmt() {
        Node nodeA = new SwitchStmt();
        Node nodeB = new SwitchStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSwitchEntry() {
        Node nodeA = new SwitchEntry();
        Node nodeB = new SwitchEntry();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenBreakStmt() {
        Node nodeA = new BreakStmt();
        Node nodeB = new BreakStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenReturnStmt() {
        Node nodeA = new ReturnStmt();
        Node nodeB = new ReturnStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenIfStmt() {
        Node nodeA = new IfStmt();
        Node nodeB = new IfStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenWhileStmt() {
        Node nodeA = new WhileStmt();
        Node nodeB = new WhileStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenContinueStmt() {
        Node nodeA = new ContinueStmt();
        Node nodeB = new ContinueStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenDoStmt() {
        Node nodeA = new DoStmt();
        Node nodeB = new DoStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenForEachStmt() {
        Node nodeA = new ForEachStmt();
        Node nodeB = new ForEachStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenForStmt() {
        Node nodeA = new ForStmt();
        Node nodeB = new ForStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenThrowStmt() {
        Node nodeA = new ThrowStmt();
        Node nodeB = new ThrowStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSynchronizedStmt() {
        Node nodeA = new SynchronizedStmt();
        Node nodeB = new SynchronizedStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenTryStmt() {
        Node nodeA = new TryStmt();
        Node nodeB = new TryStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenCatchClause() {
        Node nodeA = new CatchClause();
        Node nodeB = new CatchClause();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenLambdaExpr() {
        Node nodeA = new LambdaExpr();
        Node nodeB = new LambdaExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenMethodReferenceExpr() {
        Node nodeA = new MethodReferenceExpr();
        Node nodeB = new MethodReferenceExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenTypeExpr() {
        Node nodeA = new TypeExpr();
        Node nodeB = new TypeExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenImportDeclaration() {
        Node nodeA = new ImportDeclaration("a", false, false);
        Node nodeB = new ImportDeclaration("b", false, false);

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleDeclaration() {
        Node nodeA = new ModuleDeclaration();
        Node nodeB = new ModuleDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleRequiresDirective() {
        Node nodeA = new ModuleRequiresDirective();
        Node nodeB = new ModuleRequiresDirective();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleExportsDirective() {
        Node nodeA = new ModuleExportsDirective();
        Node nodeB = new ModuleExportsDirective();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleProvidesDirective() {
        Node nodeA = new ModuleProvidesDirective();
        Node nodeB = new ModuleProvidesDirective();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleUsesDirective() {
        Node nodeA = new ModuleUsesDirective();
        Node nodeB = new ModuleUsesDirective();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModuleOpensDirective() {
        Node nodeA = new ModuleOpensDirective();
        Node nodeB = new ModuleOpensDirective();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenUnparsableStmt() {
        Node nodeA = new UnparsableStmt();
        Node nodeB = new UnparsableStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenReceiverParameter() {
        Node nodeA = new ReceiverParameter();
        Node nodeB = new ReceiverParameter();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenVarType() {
        Node nodeA = new VarType();
        Node nodeB = new VarType();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenModifier() {
        Node nodeA = new Modifier();
        Node nodeB = new Modifier();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenSwitchExpr() {
        Node nodeA = new SwitchExpr();
        Node nodeB = new SwitchExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenYieldStmt() {
        Node nodeA = new YieldStmt();
        Node nodeB = new YieldStmt();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenTextBlockLiteralExpr() {
        Node nodeA = new TextBlockLiteralExpr();
        Node nodeB = new TextBlockLiteralExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenTypePatternExpr() {
        Node nodeA = new TypePatternExpr();
        Node nodeB = new TypePatternExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenRecordPatternExpr() {
        Node nodeA = new RecordPatternExpr();
        Node nodeB = new RecordPatternExpr();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenRecordDeclaration() {
        Node nodeA = new RecordDeclaration();
        Node nodeB = new RecordDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

    @Test
    void equals_GivenCompactConstructorDeclaration() {
        Node nodeA = new CompactConstructorDeclaration();
        Node nodeB = new CompactConstructorDeclaration();

        Assertions.assertTrue(ObjectIdentityEqualsVisitor.equals(nodeA, nodeA));
        Assertions.assertFalse(ObjectIdentityEqualsVisitor.equals(nodeA, nodeB));
    }

}
