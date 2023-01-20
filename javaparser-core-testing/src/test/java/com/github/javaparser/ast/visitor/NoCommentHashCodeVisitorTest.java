/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.ast.type.PrimitiveType.intType;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.mockito.Mockito.*;

class NoCommentHashCodeVisitorTest {

	@Test
	void testEquals() {
		CompilationUnit p1 = parse("class X { }");
		CompilationUnit p2 = parse("class X { }");
		assertEquals(p1.hashCode(), p2.hashCode());
	}

	@Test
	void testEqualsWithDifferentComments() {
		CompilationUnit p1 = parse("/* a */ class X { /** b */} //c");
		CompilationUnit p2 = parse("/* b */ class X { }  //c");
		assertEquals(p1.hashCode(), p2.hashCode());
		assertEquals(3, p1.getAllComments().size());
		assertEquals(2, p2.getAllComments().size());
	}

	@Test
	void testNotEquals() {
		CompilationUnit p1 = parse("class X { }");
		CompilationUnit p2 = parse("class Y { }");
		assertNotEquals(p1.hashCode(), p2.hashCode());
	}

	@Test
	void testJavadocCommentDoesNotHaveHashCode() {
		JavadocComment node = spy(new JavadocComment());
		assertEquals(0, NoCommentHashCodeVisitor.hashCode(node));

		verify(node).accept(isA(NoCommentHashCodeVisitor.class), isNull());
	}

	@Test
	void testLineCommentDoesNotHaveHashCode() {
		LineComment node = spy(new LineComment());
		assertEquals(0, NoCommentHashCodeVisitor.hashCode(node));

		verify(node).accept(isA(NoCommentHashCodeVisitor.class), isNull());
	}

	@Test
	void testBlockCommentDoesNotHaveHashCode() {
		BlockComment node = spy(new BlockComment());
		assertEquals(0, NoCommentHashCodeVisitor.hashCode(node));

		verify(node).accept(isA(NoCommentHashCodeVisitor.class), isNull());
	}

	@Test
	void testVisitAnnotationDeclaration() {
		AnnotationDeclaration node = spy(new AnnotationDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitAnnotationMemberDeclaration() {
		AnnotationMemberDeclaration node = spy(new AnnotationMemberDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getDefaultValue();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitArrayAccessExpr() {
		ArrayAccessExpr node = spy(new ArrayAccessExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getIndex();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitArrayCreationExpr() {
		ArrayCreationExpr node = spy(new ArrayCreationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getElementType();
		verify(node, times(2)).getInitializer();
		verify(node, times(1)).getLevels();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitArrayCreationLevel() {
		ArrayCreationLevel node = spy(new ArrayCreationLevel());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getDimension();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitArrayInitializerExpr() {
		ArrayInitializerExpr node = spy(new ArrayInitializerExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValues();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitArrayType() {
		ArrayType node = spy(new ArrayType(intType()));
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getComponentType();
		verify(node, times(1)).getOrigin();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitAssertStmt() {
		AssertStmt node = spy(new AssertStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getCheck();
		verify(node, times(1)).getMessage();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitAssignExpr() {
		AssignExpr node = spy(new AssignExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getOperator();
		verify(node, times(1)).getTarget();
		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitBinaryExpr() {
		BinaryExpr node = spy(new BinaryExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getLeft();
		verify(node, times(1)).getOperator();
		verify(node, times(1)).getRight();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitBlockStmt() {
		BlockStmt node = spy(new BlockStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getStatements();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitBooleanLiteralExpr() {
		BooleanLiteralExpr node = spy(new BooleanLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).isValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitBreakStmt() {
		BreakStmt node = spy(new BreakStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getLabel();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitCastExpr() {
		CastExpr node = spy(new CastExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitCatchClause() {
		CatchClause node = spy(new CatchClause());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getParameter();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitCharLiteralExpr() {
		CharLiteralExpr node = spy(new CharLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitClassExpr() {
		ClassExpr node = spy(new ClassExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitClassOrInterfaceDeclaration() {
		ClassOrInterfaceDeclaration node = spy(new ClassOrInterfaceDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExtendedTypes();
		verify(node, times(1)).getImplementedTypes();
		verify(node, times(1)).isInterface();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitClassOrInterfaceType() {
		ClassOrInterfaceType node = spy(new ClassOrInterfaceType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitCompilationUnit() {
		CompilationUnit node = spy(new CompilationUnit());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getImports();
		verify(node, times(1)).getModule();
		verify(node, times(1)).getPackageDeclaration();
		verify(node, times(1)).getTypes();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitConditionalExpr() {
		ConditionalExpr node = spy(new ConditionalExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getCondition();
		verify(node, times(1)).getElseExpr();
		verify(node, times(1)).getThenExpr();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitConstructorDeclaration() {
		ConstructorDeclaration node = spy(new ConstructorDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getParameters();
		verify(node, times(1)).getReceiverParameter();
		verify(node, times(1)).getThrownExceptions();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitContinueStmt() {
		ContinueStmt node = spy(new ContinueStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getLabel();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitDoStmt() {
		DoStmt node = spy(new DoStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getCondition();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitDoubleLiteralExpr() {
		DoubleLiteralExpr node = spy(new DoubleLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitEmptyStmt() {
		EmptyStmt node = spy(new EmptyStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, never()).getComment();
	}

	@Test
	void testVisitEnclosedExpr() {
		EnclosedExpr node = spy(new EnclosedExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getInner();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitEnumConstantDeclaration() {
		EnumConstantDeclaration node = spy(new EnumConstantDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getArguments();
		verify(node, times(1)).getClassBody();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitEnumDeclaration() {
		EnumDeclaration node = spy(new EnumDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getEntries();
		verify(node, times(1)).getImplementedTypes();
		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitExplicitConstructorInvocationStmt() {
		ExplicitConstructorInvocationStmt node = spy(new ExplicitConstructorInvocationStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getArguments();
		verify(node, times(1)).getExpression();
		verify(node, times(1)).isThis();
		verify(node, times(1)).getTypeArguments();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitExpressionStmt() {
		ExpressionStmt node = spy(new ExpressionStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitFieldAccessExpr() {
		FieldAccessExpr node = spy(new FieldAccessExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitFieldDeclaration() {
		FieldDeclaration node = spy(new FieldDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getVariables();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitForStmt() {
		ForStmt node = spy(new ForStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(2)).getCompare();
		verify(node, times(1)).getInitialization();
		verify(node, times(1)).getUpdate();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitForEachStmt() {
		ForEachStmt node = spy(new ForEachStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getIterable();
		verify(node, times(1)).getVariable();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitIfStmt() {
		IfStmt node = spy(new IfStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getCondition();
		verify(node, times(1)).getElseStmt();
		verify(node, times(1)).getThenStmt();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitImportDeclaration() {
		ImportDeclaration node = spy(new ImportDeclaration(new Name(), false, false));
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).isAsterisk();
		verify(node, times(1)).isStatic();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitInitializerDeclaration() {
		InitializerDeclaration node = spy(new InitializerDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).isStatic();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitInstanceOfExpr() {
		InstanceOfExpr node = spy(new InstanceOfExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, times(1)).getPattern();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitIntegerLiteralExpr() {
		IntegerLiteralExpr node = spy(new IntegerLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitIntersectionType() {
		NodeList<ReferenceType> elements = new NodeList<>();
		elements.add(new ClassOrInterfaceType());
		IntersectionType node = spy(new IntersectionType(elements));
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getElements();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitLabeledStmt() {
		LabeledStmt node = spy(new LabeledStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getLabel();
		verify(node, times(1)).getStatement();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitLambdaExpr() {
		LambdaExpr node = spy(new LambdaExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).isEnclosingParameters();
		verify(node, times(1)).getParameters();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitLocalClassDeclarationStmt() {
		LocalClassDeclarationStmt node = spy(new LocalClassDeclarationStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getClassDeclaration();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitLocalRecordDeclarationStmt() {
		LocalRecordDeclarationStmt node = spy(new LocalRecordDeclarationStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getRecordDeclaration();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitLongLiteralExpr() {
		LongLiteralExpr node = spy(new LongLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitMarkerAnnotationExpr() {
		MarkerAnnotationExpr node = spy(new MarkerAnnotationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitMemberValuePair() {
		MemberValuePair node = spy(new MemberValuePair());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitMethodCallExpr() {
		MethodCallExpr node = spy(new MethodCallExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getArguments();
		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitMethodDeclaration() {
		MethodDeclaration node = spy(new MethodDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(2)).getBody();
		verify(node, times(1)).getType();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getParameters();
		verify(node, times(1)).getReceiverParameter();
		verify(node, times(1)).getThrownExceptions();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitMethodReferenceExpr() {
		MethodReferenceExpr node = spy(new MethodReferenceExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getIdentifier();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitNameExpr() {
		NameExpr node = spy(new NameExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitName() {
		Name node = spy(new Name());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getIdentifier();
		verify(node, times(1)).getQualifier();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitNormalAnnotationExpr() {
		NormalAnnotationExpr node = spy(new NormalAnnotationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getPairs();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitNullLiteralExpr() {
		NullLiteralExpr node = spy(new NullLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, never()).getComment();
	}

	@Test
	void testVisitObjectCreationExpr() {
		ObjectCreationExpr node = spy(new ObjectCreationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnonymousClassBody();
		verify(node, times(1)).getArguments();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getType();
		verify(node, times(2)).getTypeArguments();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitPackageDeclaration() {
		PackageDeclaration node = spy(new PackageDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitParameter() {
		Parameter node = spy(new Parameter());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).isVarArgs();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getVarArgsAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitPrimitiveType() {
		PrimitiveType node = spy(new PrimitiveType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getType();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitReturnStmt() {
		ReturnStmt node = spy(new ReturnStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSimpleName() {
		SimpleName node = spy(new SimpleName());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getIdentifier();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSingleMemberAnnotationExpr() {
		SingleMemberAnnotationExpr node = spy(new SingleMemberAnnotationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getMemberValue();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitStringLiteralExpr() {
		StringLiteralExpr node = spy(new StringLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSuperExpr() {
		SuperExpr node = spy(new SuperExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getTypeName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSwitchEntry() {
		SwitchEntry node = spy(new SwitchEntry());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getLabels();
		verify(node, times(1)).getStatements();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSwitchStmt() {
		SwitchStmt node = spy(new SwitchStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getEntries();
		verify(node, times(1)).getSelector();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSynchronizedStmt() {
		SynchronizedStmt node = spy(new SynchronizedStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getExpression();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitThisExpr() {
		ThisExpr node = spy(new ThisExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getTypeName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitThrowStmt() {
		ThrowStmt node = spy(new ThrowStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitTryStmt() {
		TryStmt node = spy(new TryStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getCatchClauses();
		verify(node, times(1)).getFinallyBlock();
		verify(node, times(1)).getResources();
		verify(node, times(1)).getTryBlock();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitTypeExpr() {
		TypeExpr node = spy(new TypeExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitTypeParameter() {
		TypeParameter node = spy(new TypeParameter());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getTypeBound();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitUnaryExpr() {
		UnaryExpr node = spy(new UnaryExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, times(1)).getOperator();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitUnionType() {
		UnionType node = spy(new UnionType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getElements();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitUnknownType() {
		UnknownType node = spy(new UnknownType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitVariableDeclarationExpr() {
		VariableDeclarationExpr node = spy(new VariableDeclarationExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getVariables();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitVariableDeclarator() {
		VariableDeclarator node = spy(new VariableDeclarator());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getInitializer();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitVoidType() {
		VoidType node = spy(new VoidType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitWhileStmt() {
		WhileStmt node = spy(new WhileStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getBody();
		verify(node, times(1)).getCondition();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitWildcardType() {
		WildcardType node = spy(new WildcardType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExtendedType();
		verify(node, times(1)).getSuperType();
		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleDeclaration() {
		ModuleDeclaration node = spy(new ModuleDeclaration());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getDirectives();
		verify(node, times(1)).isOpen();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleRequiresDirective() {
		ModuleRequiresDirective node = spy(new ModuleRequiresDirective());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleExportsDirective() {
		ModuleExportsDirective node = spy(new ModuleExportsDirective());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getModuleNames();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleProvidesDirective() {
		ModuleProvidesDirective node = spy(new ModuleProvidesDirective());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getWith();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleUsesDirective() {
		ModuleUsesDirective node = spy(new ModuleUsesDirective());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModuleOpensDirective() {
		ModuleOpensDirective node = spy(new ModuleOpensDirective());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getModuleNames();
		verify(node, times(1)).getName();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitUnparsableStmt() {
		UnparsableStmt node = spy(new UnparsableStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, never()).getComment();
	}

	@Test
	void testVisitReceiverParameter() {
		ReceiverParameter node = spy(new ReceiverParameter());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitVarType() {
		VarType node = spy(new VarType());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getAnnotations();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitModifier() {
		Modifier node = spy(new Modifier());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getKeyword();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitSwitchExpr() {
		SwitchExpr node = spy(new SwitchExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getEntries();
		verify(node, times(1)).getSelector();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitYieldStmt() {
		YieldStmt node = spy(new YieldStmt());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getExpression();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitTextBlockLiteralExpr() {
		TextBlockLiteralExpr node = spy(new TextBlockLiteralExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getValue();
		verify(node, never()).getComment();
	}

	@Test
	void testVisitPatternExpr() {
		PatternExpr node = spy(new PatternExpr());
		NoCommentHashCodeVisitor.hashCode(node);

		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, never()).getComment();
	}

}
