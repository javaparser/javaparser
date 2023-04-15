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

import static com.github.javaparser.ast.type.PrimitiveType.intType;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.spy;

class ObjectIdentityHashCodeVisitorTest {

	@Test
	void testVisitAnnotationDeclaration() {
		AnnotationDeclaration node = spy(new AnnotationDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitAnnotationMemberDeclaration() {
		AnnotationMemberDeclaration node = spy(new AnnotationMemberDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitArrayAccessExpr() {
		ArrayAccessExpr node = spy(new ArrayAccessExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitArrayCreationExpr() {
		ArrayCreationExpr node = spy(new ArrayCreationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitArrayCreationLevel() {
		ArrayCreationLevel node = spy(new ArrayCreationLevel());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitArrayInitializerExpr() {
		ArrayInitializerExpr node = spy(new ArrayInitializerExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitArrayType() {
		ArrayType node = spy(new ArrayType(intType()));
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitAssertStmt() {
		AssertStmt node = spy(new AssertStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitAssignExpr() {
		AssignExpr node = spy(new AssignExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitBinaryExpr() {
		BinaryExpr node = spy(new BinaryExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitBlockComment() {
		BlockComment node = spy(new BlockComment());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitBlockStmt() {
		BlockStmt node = spy(new BlockStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitBooleanLiteralExpr() {
		BooleanLiteralExpr node = spy(new BooleanLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitBreakStmt() {
		BreakStmt node = spy(new BreakStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitCastExpr() {
		CastExpr node = spy(new CastExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitCatchClause() {
		CatchClause node = spy(new CatchClause());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitCharLiteralExpr() {
		CharLiteralExpr node = spy(new CharLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitClassExpr() {
		ClassExpr node = spy(new ClassExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitClassOrInterfaceDeclaration() {
		ClassOrInterfaceDeclaration node = spy(new ClassOrInterfaceDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitClassOrInterfaceType() {
		ClassOrInterfaceType node = spy(new ClassOrInterfaceType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitCompilationUnit() {
		CompilationUnit node = spy(new CompilationUnit());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitConditionalExpr() {
		ConditionalExpr node = spy(new ConditionalExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitConstructorDeclaration() {
		ConstructorDeclaration node = spy(new ConstructorDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitContinueStmt() {
		ContinueStmt node = spy(new ContinueStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitDoStmt() {
		DoStmt node = spy(new DoStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitDoubleLiteralExpr() {
		DoubleLiteralExpr node = spy(new DoubleLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitEmptyStmt() {
		EmptyStmt node = spy(new EmptyStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitEnclosedExpr() {
		EnclosedExpr node = spy(new EnclosedExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitEnumConstantDeclaration() {
		EnumConstantDeclaration node = spy(new EnumConstantDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitEnumDeclaration() {
		EnumDeclaration node = spy(new EnumDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitExplicitConstructorInvocationStmt() {
		ExplicitConstructorInvocationStmt node = spy(new ExplicitConstructorInvocationStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitExpressionStmt() {
		ExpressionStmt node = spy(new ExpressionStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitFieldAccessExpr() {
		FieldAccessExpr node = spy(new FieldAccessExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitFieldDeclaration() {
		FieldDeclaration node = spy(new FieldDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitForEachStmt() {
		ForEachStmt node = spy(new ForEachStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitForStmt() {
		ForStmt node = spy(new ForStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitIfStmt() {
		IfStmt node = spy(new IfStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitImportDeclaration() {
		ImportDeclaration node = spy(new ImportDeclaration(new Name(), false, false));
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitInitializerDeclaration() {
		InitializerDeclaration node = spy(new InitializerDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitInstanceOfExpr() {
		InstanceOfExpr node = spy(new InstanceOfExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitIntegerLiteralExpr() {
		IntegerLiteralExpr node = spy(new IntegerLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitIntersectionType() {
		NodeList<ReferenceType> elements = new NodeList<>();
		elements.add(new ClassOrInterfaceType());
		IntersectionType node = spy(new IntersectionType(elements));
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitJavadocComment() {
		JavadocComment node = spy(new JavadocComment());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLabeledStmt() {
		LabeledStmt node = spy(new LabeledStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLambdaExpr() {
		LambdaExpr node = spy(new LambdaExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLineComment() {
		LineComment node = spy(new LineComment());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLocalClassDeclarationStmt() {
		LocalClassDeclarationStmt node = spy(new LocalClassDeclarationStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLocalRecordDeclarationStmt() {
		LocalRecordDeclarationStmt node = spy(new LocalRecordDeclarationStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitLongLiteralExpr() {
		LongLiteralExpr node = spy(new LongLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitMarkerAnnotationExpr() {
		MarkerAnnotationExpr node = spy(new MarkerAnnotationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitMemberValuePair() {
		MemberValuePair node = spy(new MemberValuePair());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitMethodCallExpr() {
		MethodCallExpr node = spy(new MethodCallExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitMethodDeclaration() {
		MethodDeclaration node = spy(new MethodDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitMethodReferenceExpr() {
		MethodReferenceExpr node = spy(new MethodReferenceExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModifier() {
		Modifier node = spy(new Modifier());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleDeclaration() {
		ModuleDeclaration node = spy(new ModuleDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleExportsDirective() {
		ModuleExportsDirective node = spy(new ModuleExportsDirective());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleOpensDirective() {
		ModuleOpensDirective node = spy(new ModuleOpensDirective());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleProvidesDirective() {
		ModuleProvidesDirective node = spy(new ModuleProvidesDirective());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleRequiresDirective() {
		ModuleRequiresDirective node = spy(new ModuleRequiresDirective());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitModuleUsesDirective() {
		ModuleUsesDirective node = spy(new ModuleUsesDirective());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitNameExpr() {
		NameExpr node = spy(new NameExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitName() {
		Name node = spy(new Name());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitNormalAnnotationExpr() {
		NormalAnnotationExpr node = spy(new NormalAnnotationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitNullLiteralExpr() {
		NullLiteralExpr node = spy(new NullLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitObjectCreationExpr() {
		ObjectCreationExpr node = spy(new ObjectCreationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitPackageDeclaration() {
		PackageDeclaration node = spy(new PackageDeclaration());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitParameter() {
		Parameter node = spy(new Parameter());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitPatternExpr() {
		PatternExpr node = spy(new PatternExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitPrimitiveType() {
		PrimitiveType node = spy(new PrimitiveType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitReceiverParameter() {
		ReceiverParameter node = spy(new ReceiverParameter());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitReturnStmt() {
		ReturnStmt node = spy(new ReturnStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSimpleName() {
		SimpleName node = spy(new SimpleName());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSingleMemberAnnotationExpr() {
		SingleMemberAnnotationExpr node = spy(new SingleMemberAnnotationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitStringLiteralExpr() {
		StringLiteralExpr node = spy(new StringLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSuperExpr() {
		SuperExpr node = spy(new SuperExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSwitchEntry() {
		SwitchEntry node = spy(new SwitchEntry());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSwitchExpr() {
		SwitchExpr node = spy(new SwitchExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSwitchStmt() {
		SwitchStmt node = spy(new SwitchStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitSynchronizedStmt() {
		SynchronizedStmt node = spy(new SynchronizedStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitTextBlockLiteralExpr() {
		TextBlockLiteralExpr node = spy(new TextBlockLiteralExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitThisExpr() {
		ThisExpr node = spy(new ThisExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitThrowStmt() {
		ThrowStmt node = spy(new ThrowStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitTryStmt() {
		TryStmt node = spy(new TryStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitTypeExpr() {
		TypeExpr node = spy(new TypeExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitTypeParameter() {
		TypeParameter node = spy(new TypeParameter());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitUnaryExpr() {
		UnaryExpr node = spy(new UnaryExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitUnionType() {
		UnionType node = spy(new UnionType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitUnknownType() {
		UnknownType node = spy(new UnknownType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitUnparsableStmt() {
		UnparsableStmt node = spy(new UnparsableStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitVarType() {
		VarType node = spy(new VarType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitVariableDeclarationExpr() {
		VariableDeclarationExpr node = spy(new VariableDeclarationExpr());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitVariableDeclarator() {
		VariableDeclarator node = spy(new VariableDeclarator());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitVoidType() {
		VoidType node = spy(new VoidType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitWhileStmt() {
		WhileStmt node = spy(new WhileStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitWildcardType() {
		WildcardType node = spy(new WildcardType());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

	@Test
	void testVisitYieldStmt() {
		YieldStmt node = spy(new YieldStmt());
		assertEquals(node.hashCode(), ObjectIdentityHashCodeVisitor.hashCode(node));
	}

}
