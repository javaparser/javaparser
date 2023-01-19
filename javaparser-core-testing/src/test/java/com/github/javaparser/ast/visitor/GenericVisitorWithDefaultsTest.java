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

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.mockito.Mockito.*;
import static org.mockito.MockitoAnnotations.openMocks;

/**
 * This class contains the tests to validate GenericVisitorWithDefaults.
 *
 * @author 4everTheOne
 */
class GenericVisitorWithDefaultsTest {

    @Captor
    private ArgumentCaptor<Object> argumentCaptor;

    private Object argument;
    private GenericVisitorWithDefaults<Node, Object> visitor;

    @BeforeEach
    void initialize() {
        openMocks(this);

        argument = new Object();
        visitor = spy(
            new GenericVisitorWithDefaults<Node, Object>() {
                @Override
                public Node defaultAction(Node n, Object arg) {
                    super.defaultAction(n, arg);
                    return n;
                }
            }
        );
    }

    @Test
    void testThatVisitWithNodeListMethodAsParameter() {
        NodeList<Node> nodeList = new NodeList<>();
        Node node = visitor.visit(nodeList, argument);
        assertNull(node);
    }

    @Test
    void testThatVisitWithAnnotationDeclarationMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(AnnotationDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAnnotationMemberDeclarationMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(AnnotationMemberDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayAccessExprMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(ArrayAccessExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayCreationExprMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(ArrayCreationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayInitializerExprMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(ArrayInitializerExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAssertStmtMethodAsParameterCallsDefaultAction() {
        Node node = visitor.visit(mock(AssertStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithBlockStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(BlockStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithBooleanLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(BooleanLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithBreakStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(BreakStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithCastExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(CastExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithCatchClauseAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(CatchClause.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithCharLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(CharLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithClassExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ClassExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithClassOrInterfaceDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ClassOrInterfaceDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithClassOrInterfaceTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ClassOrInterfaceType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithCompilationUnitAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(CompilationUnit.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithConditionalExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ConditionalExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithConstructorDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ConstructorDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithContinueStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ContinueStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithDoStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(DoStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithDoubleLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(DoubleLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAnnotationDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(AnnotationDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAnnotationMemberDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(AnnotationMemberDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayAccessExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ArrayAccessExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayCreationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ArrayCreationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayCreationLevelAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ArrayCreationLevel.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayInitializerExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ArrayInitializerExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithArrayTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ArrayType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAssertStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(AssertStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithAssignExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(AssignExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithBinaryExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(BinaryExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithBlockCommentAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(BlockComment.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithEmptyStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(EmptyStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithEnclosedExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(EnclosedExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithEnumConstantDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(EnumConstantDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithEnumDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(EnumDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithExplicitConstructorInvocationStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ExplicitConstructorInvocationStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithExpressionStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ExpressionStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithFieldAccessExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(FieldAccessExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithFieldDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(FieldDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithForEachStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ForEachStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithForStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ForStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithIfStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(IfStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithImportDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ImportDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithInitializerDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(InitializerDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithInstanceOfExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(InstanceOfExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithIntegerLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(IntegerLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithIntersectionTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(IntersectionType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithJavadocCommentAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(JavadocComment.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLabeledStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LabeledStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLambdaExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LambdaExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLineCommentAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LineComment.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLocalClassDeclarationStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LocalClassDeclarationStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLocalRecordDeclarationStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LocalRecordDeclarationStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithLongLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(LongLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithMarkerAnnotationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(MarkerAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithMemberValuePairAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(MemberValuePair.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithMethodCallExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(MethodCallExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithMethodDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(MethodDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithMethodReferenceExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(MethodReferenceExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModifierAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(Modifier.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleExportsDirectiveAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleExportsDirective.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleOpensDirectiveAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleOpensDirective.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleProvidesDirectiveAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleProvidesDirective.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleRequiresDirectiveAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleRequiresDirective.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithModuleUsesDirectiveAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ModuleUsesDirective.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithNameExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(NameExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithNameAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(Name.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithNormalAnnotationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(NormalAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithNullLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(NullLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithObjectCreationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ObjectCreationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithPackageDeclarationAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(PackageDeclaration.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithParameterAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(Parameter.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithPatternExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(PatternExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithPrimitiveTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(PrimitiveType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithReceiverParameterAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ReceiverParameter.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithReturnStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ReturnStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSimpleNameAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SimpleName.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSingleMemberAnnotationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SingleMemberAnnotationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithStringLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(StringLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSuperExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SuperExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSwitchEntryAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SwitchEntry.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSwitchExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SwitchExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSwitchStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SwitchStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithSynchronizedStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(SynchronizedStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithTextBlockLiteralExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(TextBlockLiteralExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithThisExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ThisExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithThrowStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(ThrowStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithTryStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(TryStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithTypeExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(TypeExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithTypeParameterAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(TypeParameter.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithUnaryExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(UnaryExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithUnionTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(UnionType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithUnknownTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(UnknownType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithUnparsableStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(UnparsableStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithVarTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(VarType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithVariableDeclarationExprAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(VariableDeclarationExpr.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithVariableDeclaratorCallDefaultAction() {
        Node node = visitor.visit(mock(VariableDeclarator.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithVoidTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(VoidType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithWhileStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(WhileStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithWildcardTypeAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(WildcardType.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    @Test
    void testThatVisitWithYieldStmtAsParameterCallDefaultAction() {
        Node node = visitor.visit(mock(YieldStmt.class), argument);
        assertNodeVisitDefaultAction(node);
    }

    /**
     * Assert that at the default methods was called only once and with the same argument.
     */
    void assertNodeVisitDefaultAction(Node node) {
        // Check if the default method was only called once
        verify(visitor, times(1)).defaultAction(same(node), argumentCaptor.capture());
        // Check if the original argument was passed to the default method
        assertSame(argument, argumentCaptor.getValue());
    }

}
