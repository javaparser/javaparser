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
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import org.junit.jupiter.api.Test;
import org.mockito.InOrder;
import org.mockito.Mockito;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;

public class GenericVisitorAdapterTest {

    private final GenericVisitorAdapter<Object, Object> visitor = new GenericVisitorAdapter<Object, Object>() {};

    @Test
    void visit_GivenAnnotationDeclaration() {
        // Given
        Object argument = mock(Object.class);
        AnnotationDeclaration node = mock(AnnotationDeclaration.class);

        // When
        Mockito.when(node.getMembers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getMembers();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenAnnotationMemberDeclaration() {
        // Given
        Object argument = mock(Object.class);
        AnnotationMemberDeclaration node = mock(AnnotationMemberDeclaration.class);

        // When
        Mockito.when(node.getDefaultValue()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getDefaultValue();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getType();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenArrayAccessExpr() {
        // Given
        Object argument = mock(Object.class);
        ArrayAccessExpr node = mock(ArrayAccessExpr.class);

        // When
        Mockito.when(node.getIndex()).thenReturn(mock(Expression.class));
        Mockito.when(node.getName()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getIndex();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenArrayCreationExpr() {
        // Given
        Object argument = mock(Object.class);
        ArrayCreationExpr node = mock(ArrayCreationExpr.class);

        // When
        Mockito.when(node.getElementType()).thenReturn(mock(Type.class));
        Mockito.when(node.getInitializer()).thenReturn(Optional.of(mock(ArrayInitializerExpr.class)));
        Mockito.when(node.getLevels()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getElementType();
        order.verify(node, times(2)).getInitializer();
        order.verify(node).getLevels();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenArrayCreationLevel() {
        // Given
        Object argument = mock(Object.class);
        ArrayCreationLevel node = mock(ArrayCreationLevel.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getDimension()).thenReturn(Optional.of(mock(ArrayInitializerExpr.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getDimension();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenArrayInitializerExpr() {
        // Given
        Object argument = mock(Object.class);
        ArrayInitializerExpr node = mock(ArrayInitializerExpr.class);

        // When
        Mockito.when(node.getValues()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getValues();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenArrayType() {
        // Given
        Object argument = mock(Object.class);
        ArrayType node = mock(ArrayType.class);

        // When
        Mockito.when(node.getComponentType()).thenReturn(mock(Type.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getComponentType();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenAssertStmt() {
        // Given
        Object argument = mock(Object.class);
        AssertStmt node = mock(AssertStmt.class);

        // When
        Mockito.when(node.getCheck()).thenReturn(mock(Expression.class));
        Mockito.when(node.getMessage()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getCheck();
        order.verify(node, times(2)).getMessage();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenAssignExpr() {
        // Given
        Object argument = mock(Object.class);
        AssignExpr node = mock(AssignExpr.class);

        // When
        Mockito.when(node.getTarget()).thenReturn(mock(Expression.class));
        Mockito.when(node.getValue()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getTarget();
        order.verify(node).getValue();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenBinaryExpr() {
        // Given
        Object argument = mock(Object.class);
        BinaryExpr node = mock(BinaryExpr.class);

        // When
        Mockito.when(node.getLeft()).thenReturn(mock(Expression.class));
        Mockito.when(node.getRight()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getLeft();
        order.verify(node).getRight();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenBlockComment() {
        // Given
        Object argument = mock(Object.class);
        BlockComment node = mock(BlockComment.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenBlockStmt() {
        // Given
        Object argument = mock(Object.class);
        BlockStmt node = mock(BlockStmt.class);

        // When
        Mockito.when(node.getStatements()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getStatements();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenBooleanLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        BooleanLiteralExpr node = mock(BooleanLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenBreakStmt() {
        // Given
        Object argument = mock(Object.class);
        BreakStmt node = mock(BreakStmt.class);

        // When
        Mockito.when(node.getLabel()).thenReturn(Optional.of(mock(SimpleName.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getLabel();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenCastExpr() {
        // Given
        Object argument = mock(Object.class);
        CastExpr node = mock(CastExpr.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenCatchClause() {
        // Given
        Object argument = mock(Object.class);
        CatchClause node = mock(CatchClause.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getParameter()).thenReturn(mock(Parameter.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getParameter();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenCharLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        CharLiteralExpr node = mock(CharLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenClassExpr() {
        // Given
        Object argument = mock(Object.class);
        ClassExpr node = mock(ClassExpr.class);

        // When
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenClassOrInterfaceDeclaration() {
        // Given
        Object argument = mock(Object.class);
        ClassOrInterfaceDeclaration node = mock(ClassOrInterfaceDeclaration.class);

        // When
        Mockito.when(node.getExtendedTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getImplementedTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getPermittedTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getTypeParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getMembers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExtendedTypes();
        order.verify(node).getImplementedTypes();
        order.verify(node).getPermittedTypes();
        order.verify(node).getTypeParameters();
        order.verify(node).getMembers();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenClassOrInterfaceType() {
        // Given
        Object argument = mock(Object.class);
        ClassOrInterfaceType node = mock(ClassOrInterfaceType.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getScope()).thenReturn(Optional.of(mock(ClassOrInterfaceType.class)));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node, times(2)).getScope();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenCompilationUnit() {
        // Given
        Object argument = mock(Object.class);
        CompilationUnit node = mock(CompilationUnit.class);

        // When
        Mockito.when(node.getImports()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModule()).thenReturn(Optional.of(mock(ModuleDeclaration.class)));
        Mockito.when(node.getPackageDeclaration()).thenReturn(Optional.of(mock(PackageDeclaration.class)));
        Mockito.when(node.getTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getImports();
        order.verify(node, times(2)).getModule();
        order.verify(node, times(2)).getPackageDeclaration();
        order.verify(node).getTypes();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenConditionalExpr() {
        // Given
        Object argument = mock(Object.class);
        ConditionalExpr node = mock(ConditionalExpr.class);

        // When
        Mockito.when(node.getCondition()).thenReturn(mock(Expression.class));
        Mockito.when(node.getElseExpr()).thenReturn(mock(Expression.class));
        Mockito.when(node.getThenExpr()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getCondition();
        order.verify(node).getElseExpr();
        order.verify(node).getThenExpr();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenConstructorDeclaration() {
        // Given
        Object argument = mock(Object.class);
        ConstructorDeclaration node = mock(ConstructorDeclaration.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getReceiverParameter()).thenReturn(Optional.of(mock(ReceiverParameter.class)));
        Mockito.when(node.getThrownExceptions()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getTypeParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getParameters();
        order.verify(node, times(2)).getReceiverParameter();
        order.verify(node).getThrownExceptions();
        order.verify(node).getTypeParameters();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenContinueStmt() {
        // Given
        Object argument = mock(Object.class);
        ContinueStmt node = mock(ContinueStmt.class);

        // When
        Mockito.when(node.getLabel()).thenReturn(Optional.of(mock(SimpleName.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getLabel();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenDoStmt() {
        // Given
        Object argument = mock(Object.class);
        DoStmt node = mock(DoStmt.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(Statement.class));
        Mockito.when(node.getCondition()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getCondition();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenDoubleLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        DoubleLiteralExpr node = mock(DoubleLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenEmptyStmt() {
        // Given
        Object argument = mock(Object.class);
        EmptyStmt node = mock(EmptyStmt.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenEnclosedExpr() {
        // Given
        Object argument = mock(Object.class);
        EnclosedExpr node = mock(EnclosedExpr.class);

        // When
        Mockito.when(node.getInner()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getInner();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenEnumConstantDeclaration() {
        // Given
        Object argument = mock(Object.class);
        EnumConstantDeclaration node = mock(EnumConstantDeclaration.class);

        // When
        Mockito.when(node.getArguments()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getClassBody()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getArguments();
        order.verify(node).getClassBody();
        order.verify(node).getName();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenEnumDeclaration() {
        // Given
        Object argument = mock(Object.class);
        EnumDeclaration node = mock(EnumDeclaration.class);

        // When
        Mockito.when(node.getEntries()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getImplementedTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getMembers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getEntries();
        order.verify(node).getImplementedTypes();
        order.verify(node).getMembers();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenExplicitConstructorInvocationStmt() {
        // Given
        Object argument = mock(Object.class);
        ExplicitConstructorInvocationStmt node = mock(ExplicitConstructorInvocationStmt.class);

        // When
        Mockito.when(node.getArguments()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getExpression()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getArguments();
        order.verify(node, times(2)).getExpression();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenExpressionStmt() {
        // Given
        Object argument = mock(Object.class);
        ExpressionStmt node = mock(ExpressionStmt.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenFieldAccessExpr() {
        // Given
        Object argument = mock(Object.class);
        FieldAccessExpr node = mock(FieldAccessExpr.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getScope()).thenReturn(mock(Expression.class));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node).getScope();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenFieldDeclaration() {
        // Given
        Object argument = mock(Object.class);
        FieldDeclaration node = mock(FieldDeclaration.class);

        // When
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getVariables()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModifiers();
        order.verify(node).getVariables();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenForStmt() {
        // Given
        Object argument = mock(Object.class);
        ForStmt node = mock(ForStmt.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(Statement.class));
        Mockito.when(node.getCompare()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getInitialization()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getUpdate()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node, times(2)).getCompare();
        order.verify(node).getInitialization();
        order.verify(node).getUpdate();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenForEachStmt() {
        // Given
        Object argument = mock(Object.class);
        ForEachStmt node = mock(ForEachStmt.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(Statement.class));
        Mockito.when(node.getIterable()).thenReturn(mock(Expression.class));
        Mockito.when(node.getVariable()).thenReturn(mock(VariableDeclarationExpr.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getIterable();
        order.verify(node).getVariable();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenIfStmt() {
        // Given
        Object argument = mock(Object.class);
        IfStmt node = mock(IfStmt.class);

        // When
        Mockito.when(node.getCondition()).thenReturn(mock(ConditionalExpr.class));
        Mockito.when(node.getElseStmt()).thenReturn(Optional.of(mock(Statement.class)));
        Mockito.when(node.getThenStmt()).thenReturn(mock(Statement.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getCondition();
        order.verify(node, times(2)).getElseStmt();
        order.verify(node).getThenStmt();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenImportDeclaration() {
        // Given
        Object argument = mock(Object.class);
        ImportDeclaration node = mock(ImportDeclaration.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenInitializerDeclaration() {
        // Given
        Object argument = mock(Object.class);
        InitializerDeclaration node = mock(InitializerDeclaration.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenInstanceOfExpr() {
        // Given
        Object argument = mock(Object.class);
        InstanceOfExpr node = mock(InstanceOfExpr.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getPattern()).thenReturn(Optional.of(mock(TypePatternExpr.class)));
        Mockito.when(node.getType()).thenReturn(mock(ReferenceType.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node, times(2)).getPattern();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenIntegerLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        IntegerLiteralExpr node = mock(IntegerLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenIntersectionType() {
        // Given
        Object argument = mock(Object.class);
        IntersectionType node = mock(IntersectionType.class);

        // When
        Mockito.when(node.getElements()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getElements();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenJavadocComment() {
        // Given
        Object argument = mock(Object.class);
        JavadocComment node = mock(JavadocComment.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLabeledStmt() {
        // Given
        Object argument = mock(Object.class);
        LabeledStmt node = mock(LabeledStmt.class);

        // When
        Mockito.when(node.getLabel()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getStatement()).thenReturn(mock(Statement.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getLabel();
        order.verify(node).getStatement();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLambdaExpr() {
        // Given
        Object argument = mock(Object.class);
        LambdaExpr node = mock(LambdaExpr.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(Statement.class));
        Mockito.when(node.getParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getParameters();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLineComment() {
        // Given
        Object argument = mock(Object.class);
        LineComment node = mock(LineComment.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLocalClassDeclarationStmt() {
        // Given
        Object argument = mock(Object.class);
        LocalClassDeclarationStmt node = mock(LocalClassDeclarationStmt.class);

        // When
        Mockito.when(node.getClassDeclaration()).thenReturn(mock(ClassOrInterfaceDeclaration.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getClassDeclaration();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLocalRecordDeclarationStmt() {
        // Given
        Object argument = mock(Object.class);
        LocalRecordDeclarationStmt node = mock(LocalRecordDeclarationStmt.class);

        // When
        Mockito.when(node.getRecordDeclaration()).thenReturn(mock(RecordDeclaration.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getRecordDeclaration();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenLongLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        LongLiteralExpr node = mock(LongLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenMarkerAnnotationExpr() {
        // Given
        Object argument = mock(Object.class);
        MarkerAnnotationExpr node = mock(MarkerAnnotationExpr.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenMemberValuePair() {
        // Given
        Object argument = mock(Object.class);
        MemberValuePair node = mock(MemberValuePair.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getValue()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node).getValue();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenMethodCallExpr() {
        // Given
        Object argument = mock(Object.class);
        MethodCallExpr node = mock(MethodCallExpr.class);

        // When
        Mockito.when(node.getArguments()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getScope()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getArguments();
        order.verify(node).getName();
        order.verify(node, times(2)).getScope();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenMethodDeclaration() {
        // Given
        Object argument = mock(Object.class);
        MethodDeclaration node = mock(MethodDeclaration.class);

        // When
        Mockito.when(node.getBody()).thenReturn(Optional.of(mock(BlockStmt.class)));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getThrownExceptions()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getTypeParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getBody();
        order.verify(node).getType();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getParameters();
        order.verify(node).getThrownExceptions();
        order.verify(node).getTypeParameters();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenMethodReferenceExpr() {
        // Given
        Object argument = mock(Object.class);
        MethodReferenceExpr node = mock(MethodReferenceExpr.class);

        // When
        Mockito.when(node.getScope()).thenReturn(mock(Expression.class));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getScope();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenNameExpr() {
        // Given
        Object argument = mock(Object.class);
        NameExpr node = mock(NameExpr.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenName() {
        // Given
        Object argument = mock(Object.class);
        Name node = mock(Name.class);

        // When
        Mockito.when(node.getQualifier()).thenReturn(Optional.of(mock(Name.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getQualifier();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenNormalAnnotationExpr() {
        // Given
        Object argument = mock(Object.class);
        NormalAnnotationExpr node = mock(NormalAnnotationExpr.class);

        // When
        Mockito.when(node.getPairs()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getPairs();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenNullLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        NullLiteralExpr node = mock(NullLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenObjectCreationExpr() {
        // Given
        Object argument = mock(Object.class);
        ObjectCreationExpr node = mock(ObjectCreationExpr.class);

        // When
        Mockito.when(node.getAnonymousClassBody()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getArguments()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getScope()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getType()).thenReturn(mock(ClassOrInterfaceType.class));
        Mockito.when(node.getTypeArguments()).thenReturn(Optional.of(mock(NodeList.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getAnonymousClassBody();
        order.verify(node).getArguments();
        order.verify(node, times(2)).getScope();
        order.verify(node).getType();
        order.verify(node, times(2)).getTypeArguments();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenPackageDeclaration() {
        // Given
        Object argument = mock(Object.class);
        PackageDeclaration node = mock(PackageDeclaration.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenParameter() {
        // Given
        Object argument = mock(Object.class);
        Parameter node = mock(Parameter.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getVarArgsAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getType();
        order.verify(node).getVarArgsAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenPrimitiveType() {
        // Given
        Object argument = mock(Object.class);
        PrimitiveType node = mock(PrimitiveType.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenReturnStmt() {
        // Given
        Object argument = mock(Object.class);
        ReturnStmt node = mock(ReturnStmt.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSimpleName() {
        // Given
        Object argument = mock(Object.class);
        SimpleName node = mock(SimpleName.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSingleMemberAnnotationExpr() {
        // Given
        Object argument = mock(Object.class);
        SingleMemberAnnotationExpr node = mock(SingleMemberAnnotationExpr.class);

        // When
        Mockito.when(node.getMemberValue()).thenReturn(mock(Expression.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getMemberValue();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenStringLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        StringLiteralExpr node = mock(StringLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSuperExpr() {
        // Given
        Object argument = mock(Object.class);
        SuperExpr node = mock(SuperExpr.class);

        // When
        Mockito.when(node.getTypeName()).thenReturn(Optional.of(mock(Name.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getTypeName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSwitchEntry() {
        // Given
        Object argument = mock(Object.class);
        SwitchEntry node = mock(SwitchEntry.class);

        // When
        Mockito.when(node.getLabels()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getStatements()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getLabels();
        order.verify(node).getStatements();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSwitchStmt() {
        // Given
        Object argument = mock(Object.class);
        SwitchStmt node = mock(SwitchStmt.class);

        // When
        Mockito.when(node.getEntries()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getSelector()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getEntries();
        order.verify(node).getSelector();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSynchronizedStmt() {
        // Given
        Object argument = mock(Object.class);
        SynchronizedStmt node = mock(SynchronizedStmt.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenThisExpr() {
        // Given
        Object argument = mock(Object.class);
        ThisExpr node = mock(ThisExpr.class);

        // When
        Mockito.when(node.getTypeName()).thenReturn(Optional.of(mock(Name.class)));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getTypeName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenThrowStmt() {
        // Given
        Object argument = mock(Object.class);
        ThrowStmt node = mock(ThrowStmt.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenTryStmt() {
        // Given
        Object argument = mock(Object.class);
        TryStmt node = mock(TryStmt.class);

        // When
        Mockito.when(node.getCatchClauses()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getFinallyBlock()).thenReturn(Optional.of(mock(BlockStmt.class)));
        Mockito.when(node.getResources()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getTryBlock()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getCatchClauses();
        order.verify(node, times(2)).getFinallyBlock();
        order.verify(node).getResources();
        order.verify(node).getTryBlock();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenTypeExpr() {
        // Given
        Object argument = mock(Object.class);
        TypeExpr node = mock(TypeExpr.class);

        // When
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenTypeParameter() {
        // Given
        Object argument = mock(Object.class);
        TypeParameter node = mock(TypeParameter.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getTypeBound()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node).getTypeBound();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenUnaryExpr() {
        // Given
        Object argument = mock(Object.class);
        UnaryExpr node = mock(UnaryExpr.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenUnionType() {
        // Given
        Object argument = mock(Object.class);
        UnionType node = mock(UnionType.class);

        // When
        Mockito.when(node.getElements()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getElements();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenUnknownType() {
        // Given
        Object argument = mock(Object.class);
        UnknownType node = mock(UnknownType.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenVariableDeclarationExpr() {
        // Given
        Object argument = mock(Object.class);
        VariableDeclarationExpr node = mock(VariableDeclarationExpr.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getVariables()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node).getModifiers();
        order.verify(node).getVariables();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenVariableDeclarator() {
        // Given
        Object argument = mock(Object.class);
        VariableDeclarator node = mock(VariableDeclarator.class);

        // When
        Mockito.when(node.getInitializer()).thenReturn(Optional.of(mock(Expression.class)));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getInitializer();
        order.verify(node).getName();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenVoidType() {
        // Given
        Object argument = mock(Object.class);
        VoidType node = mock(VoidType.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenWhileStmt() {
        // Given
        Object argument = mock(Object.class);
        WhileStmt node = mock(WhileStmt.class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(Statement.class));
        Mockito.when(node.getCondition()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getCondition();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenWildcardType() {
        // Given
        Object argument = mock(Object.class);
        WildcardType node = mock(WildcardType.class);

        // When
        Mockito.when(node.getExtendedType()).thenReturn(Optional.of(mock(ReferenceType.class)));
        Mockito.when(node.getSuperType()).thenReturn(Optional.of(mock(ReferenceType.class)));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getExtendedType();
        order.verify(node, times(2)).getSuperType();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleDeclaration() {
        // Given
        Object argument = mock(Object.class);
        ModuleDeclaration node = mock(ModuleDeclaration.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getDirectives()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node).getDirectives();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleExportsDirective() {
        // Given
        Object argument = mock(Object.class);
        ModuleExportsDirective node = mock(ModuleExportsDirective.class);

        // When
        Mockito.when(node.getModuleNames()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModuleNames();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleOpensDirective() {
        // Given
        Object argument = mock(Object.class);
        ModuleOpensDirective node = mock(ModuleOpensDirective.class);

        // When
        Mockito.when(node.getModuleNames()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModuleNames();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleProvidesDirective() {
        // Given
        Object argument = mock(Object.class);
        ModuleProvidesDirective node = mock(ModuleProvidesDirective.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getWith()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node).getWith();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleRequiresDirective() {
        // Given
        Object argument = mock(Object.class);
        ModuleRequiresDirective node = mock(ModuleRequiresDirective.class);

        // When
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModuleUsesDirective() {
        // Given
        Object argument = mock(Object.class);
        ModuleUsesDirective node = mock(ModuleUsesDirective.class);

        // When
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getName();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenUnparsableStmt() {
        // Given
        Object argument = mock(Object.class);
        UnparsableStmt node = mock(UnparsableStmt.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenReceiverParameter() {
        // Given
        Object argument = mock(Object.class);
        ReceiverParameter node = mock(ReceiverParameter.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(Name.class));
        Mockito.when(node.getType()).thenReturn(mock(Type.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node).getName();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenVarType() {
        // Given
        Object argument = mock(Object.class);
        VarType node = mock(VarType.class);

        // When
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenModifier() {
        // Given
        Object argument = mock(Object.class);
        Modifier node = mock(Modifier.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenSwitchExpr() {
        // Given
        Object argument = mock(Object.class);
        SwitchExpr node = mock(SwitchExpr.class);

        // When
        Mockito.when(node.getEntries()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getSelector()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getEntries();
        order.verify(node).getSelector();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenYieldStmt() {
        // Given
        Object argument = mock(Object.class);
        YieldStmt node = mock(YieldStmt.class);

        // When
        Mockito.when(node.getExpression()).thenReturn(mock(Expression.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getExpression();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenTextBlockLiteralExpr() {
        // Given
        Object argument = mock(Object.class);
        TextBlockLiteralExpr node = mock(TextBlockLiteralExpr.class);

        // When
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenTypePatternExpr() {
        // Given
        Object argument = mock(Object.class);
        TypePatternExpr node = mock(TypePatternExpr.class);

        // When
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getType()).thenReturn(mock(ReferenceType.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenRecordPatternExpr() {
        // Given
        Object argument = mock(Object.class);
        RecordPatternExpr node = mock(RecordPatternExpr.class);

        // When
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getType()).thenReturn(mock(ReferenceType.class));
        Mockito.when(node.getPatternList()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getModifiers();
        order.verify(node).getPatternList();
        order.verify(node).getType();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_GivenRecordDeclaration() {
        // Given
        Object argument = mock(Object.class);
        RecordDeclaration node = mock(RecordDeclaration.class);

        // When
        Mockito.when(node.getImplementedTypes()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getReceiverParameter()).thenReturn(Optional.of(mock(ReceiverParameter.class)));
        Mockito.when(node.getTypeParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getMembers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getImplementedTypes();
        order.verify(node).getParameters();
        order.verify(node, times(2)).getReceiverParameter();
        order.verify(node).getTypeParameters();
        order.verify(node).getMembers();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

    @Test
    void visit_CompactConstructorDeclaration () {
        // Given
        Object argument = mock(Object.class);
        CompactConstructorDeclaration  node = mock(CompactConstructorDeclaration .class);

        // When
        Mockito.when(node.getBody()).thenReturn(mock(BlockStmt.class));
        Mockito.when(node.getModifiers()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getName()).thenReturn(mock(SimpleName.class));
        Mockito.when(node.getThrownExceptions()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getTypeParameters()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getAnnotations()).thenReturn(mock(NodeList.class));
        Mockito.when(node.getComment()).thenReturn(Optional.of(mock(Comment.class)));

        // Then
        Object result = visitor.visit(node, argument);

        // Assert
        assertNull(result);

        // Verify
        InOrder order = Mockito.inOrder(node);
        order.verify(node).getBody();
        order.verify(node).getModifiers();
        order.verify(node).getName();
        order.verify(node).getThrownExceptions();
        order.verify(node).getTypeParameters();
        order.verify(node).getAnnotations();
        order.verify(node, times(2)).getComment();
        order.verifyNoMoreInteractions();
    }

}
