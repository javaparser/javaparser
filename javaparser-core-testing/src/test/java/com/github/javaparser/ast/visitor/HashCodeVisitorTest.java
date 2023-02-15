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

class HashCodeVisitorTest {

	@Test
	void testEquals() {
		CompilationUnit p1 = parse("class X { }");
		CompilationUnit p2 = parse("class X { }");
		assertEquals(p1.hashCode(), p2.hashCode());
	}

	@Test
	void testNotEquals() {
		CompilationUnit p1 = parse("class X { }");
		CompilationUnit p2 = parse("class Y { }");
		assertNotEquals(p1.hashCode(), p2.hashCode());
	}

	@Test
	void testVisitAnnotationDeclaration() {
		AnnotationDeclaration node = spy(new AnnotationDeclaration());
		HashCodeVisitor.hashCode(node);

		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitAnnotationMemberDeclaration() {
		AnnotationMemberDeclaration node = spy(new AnnotationMemberDeclaration());
		HashCodeVisitor.hashCode(node);

		verify(node, times(1)).getDefaultValue();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitArrayAccessExpr() {
		ArrayAccessExpr node = spy(new ArrayAccessExpr());
		HashCodeVisitor.hashCode(node);

		verify(node, times(1)).getIndex();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitArrayCreationExpr() {
		ArrayCreationExpr node = spy(new ArrayCreationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getElementType();
		verify(node, times(2)).getInitializer();
		verify(node, times(1)).getLevels();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitArrayCreationLevel() {
		ArrayCreationLevel node = spy(new ArrayCreationLevel());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getDimension();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitArrayInitializerExpr() {
		ArrayInitializerExpr node = spy(new ArrayInitializerExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValues();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitArrayType() {
		ArrayType node = spy(new ArrayType(intType()));
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getComponentType();
		verify(node, times(1)).getOrigin();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitAssertStmt() {
		AssertStmt node = spy(new AssertStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getCheck();
		verify(node, times(1)).getMessage();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitAssignExpr() {
		AssignExpr node = spy(new AssignExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getOperator();
		verify(node, times(1)).getTarget();
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitBinaryExpr() {
		BinaryExpr node = spy(new BinaryExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getLeft();
		verify(node, times(1)).getOperator();
		verify(node, times(1)).getRight();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitBlockComment() {
		BlockComment node = spy(new BlockComment());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getContent();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitBlockStmt() {
		BlockStmt node = spy(new BlockStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getStatements();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitBooleanLiteralExpr() {
		BooleanLiteralExpr node = spy(new BooleanLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).isValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitBreakStmt() {
		BreakStmt node = spy(new BreakStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getLabel();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitCastExpr() {
		CastExpr node = spy(new CastExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitCatchClause() {
		CatchClause node = spy(new CatchClause());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getParameter();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitCharLiteralExpr() {
		CharLiteralExpr node = spy(new CharLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitClassExpr() {
		ClassExpr node = spy(new ClassExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitClassOrInterfaceDeclaration() {
		ClassOrInterfaceDeclaration node = spy(new ClassOrInterfaceDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExtendedTypes();
		verify(node, times(1)).getImplementedTypes();
		verify(node, times(1)).isInterface();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitClassOrInterfaceType() {
		ClassOrInterfaceType node = spy(new ClassOrInterfaceType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitCompilationUnit() {
		CompilationUnit node = spy(new CompilationUnit());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getImports();
		verify(node, times(1)).getModule();
		verify(node, times(1)).getPackageDeclaration();
		verify(node, times(1)).getTypes();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitConditionalExpr() {
		ConditionalExpr node = spy(new ConditionalExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getCondition();
		verify(node, times(1)).getElseExpr();
		verify(node, times(1)).getThenExpr();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitConstructorDeclaration() {
		ConstructorDeclaration node = spy(new ConstructorDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getParameters();
		verify(node, times(1)).getReceiverParameter();
		verify(node, times(1)).getThrownExceptions();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitContinueStmt() {
		ContinueStmt node = spy(new ContinueStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getLabel();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitDoStmt() {
		DoStmt node = spy(new DoStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getCondition();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitDoubleLiteralExpr() {
		DoubleLiteralExpr node = spy(new DoubleLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitEmptyStmt() {
		EmptyStmt node = spy(new EmptyStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitEnclosedExpr() {
		EnclosedExpr node = spy(new EnclosedExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getInner();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitEnumConstantDeclaration() {
		EnumConstantDeclaration node = spy(new EnumConstantDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getArguments();
		verify(node, times(1)).getClassBody();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitEnumDeclaration() {
		EnumDeclaration node = spy(new EnumDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getEntries();
		verify(node, times(1)).getImplementedTypes();
		verify(node, times(1)).getMembers();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitExplicitConstructorInvocationStmt() {
		ExplicitConstructorInvocationStmt node = spy(new ExplicitConstructorInvocationStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getArguments();
		verify(node, times(1)).getExpression();
		verify(node, times(1)).isThis();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitExpressionStmt() {
		ExpressionStmt node = spy(new ExpressionStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitFieldAccessExpr() {
		FieldAccessExpr node = spy(new FieldAccessExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitFieldDeclaration() {
		FieldDeclaration node = spy(new FieldDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getVariables();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitForEachStmt() {
		ForEachStmt node = spy(new ForEachStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getIterable();
		verify(node, times(1)).getVariable();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitForStmt() {
		ForStmt node = spy(new ForStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(2)).getCompare();
		verify(node, times(1)).getInitialization();
		verify(node, times(1)).getUpdate();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitIfStmt() {
		IfStmt node = spy(new IfStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getCondition();
		verify(node, times(1)).getElseStmt();
		verify(node, times(1)).getThenStmt();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitImportDeclaration() {
		ImportDeclaration node = spy(new ImportDeclaration(new Name(), false, false));
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).isAsterisk();
		verify(node, times(1)).isStatic();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitInitializerDeclaration() {
		InitializerDeclaration node = spy(new InitializerDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).isStatic();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitInstanceOfExpr() {
		InstanceOfExpr node = spy(new InstanceOfExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getPattern();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitIntegerLiteralExpr() {
		IntegerLiteralExpr node = spy(new IntegerLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitIntersectionType() {
		NodeList<ReferenceType> elements = new NodeList<>();
		elements.add(new ClassOrInterfaceType());
		IntersectionType node = spy(new IntersectionType(elements));
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getElements();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitJavadocComment() {
		JavadocComment node = spy(new JavadocComment());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getContent();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLabeledStmt() {
		LabeledStmt node = spy(new LabeledStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getLabel();
		verify(node, times(1)).getStatement();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLambdaExpr() {
		LambdaExpr node = spy(new LambdaExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).isEnclosingParameters();
		verify(node, times(1)).getParameters();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLineComment() {
		LineComment node = spy(new LineComment());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getContent();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLocalClassDeclarationStmt() {
		LocalClassDeclarationStmt node = spy(new LocalClassDeclarationStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getClassDeclaration();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLocalRecordDeclarationStmt() {
		LocalRecordDeclarationStmt node = spy(new LocalRecordDeclarationStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getRecordDeclaration();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitLongLiteralExpr() {
		LongLiteralExpr node = spy(new LongLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitMarkerAnnotationExpr() {
		MarkerAnnotationExpr node = spy(new MarkerAnnotationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitMemberValuePair() {
		MemberValuePair node = spy(new MemberValuePair());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitMethodCallExpr() {
		MethodCallExpr node = spy(new MethodCallExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getArguments();
		verify(node, times(1)).getName();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitMethodDeclaration() {
		MethodDeclaration node = spy(new MethodDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(2)).getBody();
		verify(node, times(1)).getType();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getParameters();
		verify(node, times(1)).getReceiverParameter();
		verify(node, times(1)).getThrownExceptions();
		verify(node, times(1)).getTypeParameters();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitMethodReferenceExpr() {
		MethodReferenceExpr node = spy(new MethodReferenceExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getIdentifier();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getTypeArguments();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModifier() {
		Modifier node = spy(new Modifier());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getKeyword();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleDeclaration() {
		ModuleDeclaration node = spy(new ModuleDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getDirectives();
		verify(node, times(1)).isOpen();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleExportsDirective() {
		ModuleExportsDirective node = spy(new ModuleExportsDirective());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getModuleNames();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleOpensDirective() {
		ModuleOpensDirective node = spy(new ModuleOpensDirective());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getModuleNames();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleProvidesDirective() {
		ModuleProvidesDirective node = spy(new ModuleProvidesDirective());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getWith();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleRequiresDirective() {
		ModuleRequiresDirective node = spy(new ModuleRequiresDirective());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitModuleUsesDirective() {
		ModuleUsesDirective node = spy(new ModuleUsesDirective());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitNameExpr() {
		NameExpr node = spy(new NameExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitName() {
		Name node = spy(new Name());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getIdentifier();
		verify(node, times(1)).getQualifier();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitNormalAnnotationExpr() {
		NormalAnnotationExpr node = spy(new NormalAnnotationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getPairs();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitNullLiteralExpr() {
		NullLiteralExpr node = spy(new NullLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitObjectCreationExpr() {
		ObjectCreationExpr node = spy(new ObjectCreationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnonymousClassBody();
		verify(node, times(1)).getArguments();
		verify(node, times(1)).getScope();
		verify(node, times(1)).getType();
		verify(node, times(2)).getTypeArguments();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitPackageDeclaration() {
		PackageDeclaration node = spy(new PackageDeclaration());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitParameter() {
		Parameter node = spy(new Parameter());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).isVarArgs();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getVarArgsAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitPatternExpr() {
		PatternExpr node = spy(new PatternExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitPrimitiveType() {
		PrimitiveType node = spy(new PrimitiveType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getType();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitReceiverParameter() {
		ReceiverParameter node = spy(new ReceiverParameter());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitReturnStmt() {
		ReturnStmt node = spy(new ReturnStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSimpleName() {
		SimpleName node = spy(new SimpleName());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getIdentifier();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSingleMemberAnnotationExpr() {
		SingleMemberAnnotationExpr node = spy(new SingleMemberAnnotationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getMemberValue();
		verify(node, times(1)).getName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitStringLiteralExpr() {
		StringLiteralExpr node = spy(new StringLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSuperExpr() {
		SuperExpr node = spy(new SuperExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getTypeName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSwitchEntry() {
		SwitchEntry node = spy(new SwitchEntry());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getLabels();
		verify(node, times(1)).getStatements();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSwitchExpr() {
		SwitchExpr node = spy(new SwitchExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getEntries();
		verify(node, times(1)).getSelector();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSwitchStmt() {
		SwitchStmt node = spy(new SwitchStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getEntries();
		verify(node, times(1)).getSelector();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitSynchronizedStmt() {
		SynchronizedStmt node = spy(new SynchronizedStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitTextBlockLiteralExpr() {
		TextBlockLiteralExpr node = spy(new TextBlockLiteralExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getValue();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitThisExpr() {
		ThisExpr node = spy(new ThisExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getTypeName();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitThrowStmt() {
		ThrowStmt node = spy(new ThrowStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitTryStmt() {
		TryStmt node = spy(new TryStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getCatchClauses();
		verify(node, times(1)).getFinallyBlock();
		verify(node, times(1)).getResources();
		verify(node, times(1)).getTryBlock();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitTypeExpr() {
		TypeExpr node = spy(new TypeExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitTypeParameter() {
		TypeParameter node = spy(new TypeParameter());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getName();
		verify(node, times(1)).getTypeBound();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitUnaryExpr() {
		UnaryExpr node = spy(new UnaryExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getOperator();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitUnionType() {
		UnionType node = spy(new UnionType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getElements();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitUnknownType() {
		UnknownType node = spy(new UnknownType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitUnparsableStmt() {
		UnparsableStmt node = spy(new UnparsableStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitVarType() {
		VarType node = spy(new VarType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitVariableDeclarationExpr() {
		VariableDeclarationExpr node = spy(new VariableDeclarationExpr());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getModifiers();
		verify(node, times(1)).getVariables();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitVariableDeclarator() {
		VariableDeclarator node = spy(new VariableDeclarator());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getInitializer();
		verify(node, times(1)).getName();
		verify(node, times(1)).getType();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitVoidType() {
		VoidType node = spy(new VoidType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitWhileStmt() {
		WhileStmt node = spy(new WhileStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getBody();
		verify(node, times(1)).getCondition();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitWildcardType() {
		WildcardType node = spy(new WildcardType());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExtendedType();
		verify(node, times(1)).getSuperType();
		verify(node, times(1)).getAnnotations();
		verify(node, times(1)).getComment();
	}

	@Test
	void testVisitYieldStmt() {
		YieldStmt node = spy(new YieldStmt());
		HashCodeVisitor.hashCode(node);
		verify(node, times(1)).getExpression();
		verify(node, times(1)).getComment();
	}

}
