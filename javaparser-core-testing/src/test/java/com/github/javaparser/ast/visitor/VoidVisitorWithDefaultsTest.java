/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General License as published by
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
 * GNU Lesser General License for more details.
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
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.mockito.Captor;

import static org.junit.jupiter.api.Assertions.assertSame;
import static org.mockito.Mockito.*;
import static org.mockito.MockitoAnnotations.openMocks;

/**
 * This class contains the tests to validate VoidVisitorWithDefaults.
 *
 * @author 4everTheOne
 */
class VoidVisitorWithDefaultsTest {

    @Captor
    private ArgumentCaptor<Object> argumentCaptor;

    private Object argument;
    private VoidVisitorWithDefaults<Object> visitor;

    @BeforeEach
    void initialize() {
        openMocks(this);

        argument = new Object();
        visitor = spy(
            new VoidVisitorWithDefaults<Object>() {}
        );
    }

    @Test
    void testThatVisitWithNodeListMethodAsParameter() {
        NodeList<Node> nodeList = new NodeList<>();
        visitor.visit(nodeList, argument);

        // Verify that the call was executed
        verify(visitor, times(1)).visit(same(nodeList), argumentCaptor.capture());
        verify(visitor, times(1)).defaultAction(same(nodeList), same(argumentCaptor.getValue()));
        assertSame(argument, argumentCaptor.getValue());
        verifyNoMoreInteractions(visitor);
    }

    @Test
    void testThatVisitWithAnnotationDeclarationMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(AnnotationDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAnnotationMemberDeclarationMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(AnnotationMemberDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayAccessExprMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(ArrayAccessExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayCreationExprMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(ArrayCreationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayInitializerExprMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(ArrayInitializerExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAssertStmtMethodAsParameterCallsDefaultAction() {
        visitor.visit(mock(AssertStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithBlockStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(BlockStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithBooleanLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(BooleanLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithBreakStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(BreakStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithCastExprAsParameterCallDefaultAction() {
        visitor.visit(mock(CastExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithCatchClauseAsParameterCallDefaultAction() {
        visitor.visit(mock(CatchClause.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithCharLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(CharLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithClassExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ClassExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithClassOrInterfaceDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(ClassOrInterfaceDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithClassOrInterfaceTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(ClassOrInterfaceType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithCompilationUnitAsParameterCallDefaultAction() {
        visitor.visit(mock(CompilationUnit.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithConditionalExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ConditionalExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithConstructorDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(ConstructorDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithContinueStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ContinueStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithDoStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(DoStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithDoubleLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(DoubleLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAnnotationDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(AnnotationDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAnnotationMemberDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(AnnotationMemberDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayAccessExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ArrayAccessExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayCreationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ArrayCreationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayCreationLevelAsParameterCallDefaultAction() {
        visitor.visit(mock(ArrayCreationLevel.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayInitializerExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ArrayInitializerExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithArrayTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(ArrayType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAssertStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(AssertStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithAssignExprAsParameterCallDefaultAction() {
        visitor.visit(mock(AssignExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithBinaryExprAsParameterCallDefaultAction() {
        visitor.visit(mock(BinaryExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithBlockCommentAsParameterCallDefaultAction() {
        visitor.visit(mock(BlockComment.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithEmptyStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(EmptyStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithEnclosedExprAsParameterCallDefaultAction() {
        visitor.visit(mock(EnclosedExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithEnumConstantDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(EnumConstantDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithEnumDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(EnumDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithExplicitConstructorInvocationStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ExplicitConstructorInvocationStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithExpressionStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ExpressionStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithFieldAccessExprAsParameterCallDefaultAction() {
        visitor.visit(mock(FieldAccessExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithFieldDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(FieldDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithForEachStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ForEachStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithForStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ForStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithIfStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(IfStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithImportDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(ImportDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithInitializerDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(InitializerDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithInstanceOfExprAsParameterCallDefaultAction() {
        visitor.visit(mock(InstanceOfExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithIntegerLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(IntegerLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithIntersectionTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(IntersectionType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithJavadocCommentAsParameterCallDefaultAction() {
        visitor.visit(mock(JavadocComment.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLabeledStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(LabeledStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLambdaExprAsParameterCallDefaultAction() {
        visitor.visit(mock(LambdaExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLineCommentAsParameterCallDefaultAction() {
        visitor.visit(mock(LineComment.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLocalClassDeclarationStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(LocalClassDeclarationStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLocalRecordDeclarationStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(LocalRecordDeclarationStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithLongLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(LongLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithMarkerAnnotationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(MarkerAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithMemberValuePairAsParameterCallDefaultAction() {
        visitor.visit(mock(MemberValuePair.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithMethodCallExprAsParameterCallDefaultAction() {
        visitor.visit(mock(MethodCallExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithMethodDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(MethodDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithMethodReferenceExprAsParameterCallDefaultAction() {
        visitor.visit(mock(MethodReferenceExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModifierAsParameterCallDefaultAction() {
        visitor.visit(mock(Modifier.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleExportsDirectiveAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleExportsDirective.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleOpensDirectiveAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleOpensDirective.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleProvidesDirectiveAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleProvidesDirective.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleRequiresDirectiveAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleRequiresDirective.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithModuleUsesDirectiveAsParameterCallDefaultAction() {
        visitor.visit(mock(ModuleUsesDirective.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithNameExprAsParameterCallDefaultAction() {
        visitor.visit(mock(NameExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithNameAsParameterCallDefaultAction() {
        visitor.visit(mock(Name.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithNormalAnnotationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(NormalAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithNullLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(NullLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithObjectCreationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ObjectCreationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithPackageDeclarationAsParameterCallDefaultAction() {
        visitor.visit(mock(PackageDeclaration.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithParameterAsParameterCallDefaultAction() {
        visitor.visit(mock(Parameter.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithPatternExprAsParameterCallDefaultAction() {
        visitor.visit(mock(PatternExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithPrimitiveTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(PrimitiveType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithReceiverParameterAsParameterCallDefaultAction() {
        visitor.visit(mock(ReceiverParameter.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithReturnStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ReturnStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSimpleNameAsParameterCallDefaultAction() {
        visitor.visit(mock(SimpleName.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSingleMemberAnnotationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(SingleMemberAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithStringLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(StringLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSuperExprAsParameterCallDefaultAction() {
        visitor.visit(mock(SuperExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSwitchEntryAsParameterCallDefaultAction() {
        visitor.visit(mock(SwitchEntry.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSwitchExprAsParameterCallDefaultAction() {
        visitor.visit(mock(SwitchExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSwitchStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(SwitchStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithSynchronizedStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(SynchronizedStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithTextBlockLiteralExprAsParameterCallDefaultAction() {
        visitor.visit(mock(TextBlockLiteralExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithThisExprAsParameterCallDefaultAction() {
        visitor.visit(mock(ThisExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithThrowStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(ThrowStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithTryStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(TryStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithTypeExprAsParameterCallDefaultAction() {
        visitor.visit(mock(TypeExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithTypeParameterAsParameterCallDefaultAction() {
        visitor.visit(mock(TypeParameter.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithUnaryExprAsParameterCallDefaultAction() {
        visitor.visit(mock(UnaryExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithUnionTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(UnionType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithUnknownTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(UnknownType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithUnparsableStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(UnparsableStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithVarTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(VarType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithVariableDeclarationExprAsParameterCallDefaultAction() {
        visitor.visit(mock(VariableDeclarationExpr.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithVariableDeclaratorCallDefaultAction() {
        visitor.visit(mock(VariableDeclarator.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithVoidTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(VoidType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithWhileStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(WhileStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithWildcardTypeAsParameterCallDefaultAction() {
        visitor.visit(mock(WildcardType.class), argument);
        assertNodeVisitDefaultAction();
    }

    @Test
    void testThatVisitWithYieldStmtAsParameterCallDefaultAction() {
        visitor.visit(mock(YieldStmt.class), argument);
        assertNodeVisitDefaultAction();
    }

    /**
     * Assert that at the default methods was called only once and with the same argument.
     */
    void assertNodeVisitDefaultAction() {
        // Check if the default method was only called once
        verify(visitor, times(1)).defaultAction(isA(Node.class), argumentCaptor.capture());
        // Check if the original argument was passed to the default method
        assertSame(argument, argumentCaptor.getValue());
    }

}
