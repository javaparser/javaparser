/*
 * Copyright (C) 2010 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 17/01/2010
 */
package japa.parser.ast.visitor;

import japa.parser.ast.BlockComment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
import japa.parser.ast.body.BaseParameter;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import japa.parser.ast.body.EmptyMemberDeclaration;
import japa.parser.ast.body.EmptyTypeDeclaration;
import japa.parser.ast.body.EnumConstantDeclaration;
import japa.parser.ast.body.EnumDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.InitializerDeclaration;
import japa.parser.ast.body.JavadocComment;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.MultiTypeParameter;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.ArrayAccessExpr;
import japa.parser.ast.expr.ArrayCreationExpr;
import japa.parser.ast.expr.ArrayInitializerExpr;
import japa.parser.ast.expr.AssignExpr;
import japa.parser.ast.expr.BinaryExpr;
import japa.parser.ast.expr.BooleanLiteralExpr;
import japa.parser.ast.expr.CastExpr;
import japa.parser.ast.expr.CharLiteralExpr;
import japa.parser.ast.expr.ClassExpr;
import japa.parser.ast.expr.ConditionalExpr;
import japa.parser.ast.expr.DoubleLiteralExpr;
import japa.parser.ast.expr.EnclosedExpr;
import japa.parser.ast.expr.FieldAccessExpr;
import japa.parser.ast.expr.InstanceOfExpr;
import japa.parser.ast.expr.IntegerLiteralExpr;
import japa.parser.ast.expr.IntegerLiteralMinValueExpr;
import japa.parser.ast.expr.LongLiteralExpr;
import japa.parser.ast.expr.LongLiteralMinValueExpr;
import japa.parser.ast.expr.MarkerAnnotationExpr;
import japa.parser.ast.expr.MemberValuePair;
import japa.parser.ast.expr.MethodCallExpr;
import japa.parser.ast.expr.NameExpr;
import japa.parser.ast.expr.NormalAnnotationExpr;
import japa.parser.ast.expr.NullLiteralExpr;
import japa.parser.ast.expr.ObjectCreationExpr;
import japa.parser.ast.expr.QualifiedNameExpr;
import japa.parser.ast.expr.SingleMemberAnnotationExpr;
import japa.parser.ast.expr.StringLiteralExpr;
import japa.parser.ast.expr.SuperExpr;
import japa.parser.ast.expr.ThisExpr;
import japa.parser.ast.expr.UnaryExpr;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.AssertStmt;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.BreakStmt;
import japa.parser.ast.stmt.CatchClause;
import japa.parser.ast.stmt.ContinueStmt;
import japa.parser.ast.stmt.DoStmt;
import japa.parser.ast.stmt.EmptyStmt;
import japa.parser.ast.stmt.ExplicitConstructorInvocationStmt;
import japa.parser.ast.stmt.ExpressionStmt;
import japa.parser.ast.stmt.ForStmt;
import japa.parser.ast.stmt.ForeachStmt;
import japa.parser.ast.stmt.IfStmt;
import japa.parser.ast.stmt.LabeledStmt;
import japa.parser.ast.stmt.ReturnStmt;
import japa.parser.ast.stmt.SwitchEntryStmt;
import japa.parser.ast.stmt.SwitchStmt;
import japa.parser.ast.stmt.SynchronizedStmt;
import japa.parser.ast.stmt.ThrowStmt;
import japa.parser.ast.stmt.TryStmt;
import japa.parser.ast.stmt.TypeDeclarationStmt;
import japa.parser.ast.stmt.WhileStmt;
import japa.parser.ast.type.ClassOrInterfaceType;
import japa.parser.ast.type.PrimitiveType;
import japa.parser.ast.type.ReferenceType;
import japa.parser.ast.type.Type;
import japa.parser.ast.type.VoidType;
import japa.parser.ast.type.WildcardType;

import java.util.Iterator;
import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public class EqualsVisitor implements GenericVisitor<Boolean, Node> {

	private static final EqualsVisitor SINGLETON = new EqualsVisitor();

	public static boolean equals(final Node n1, final Node n2) {
		return SINGLETON.nodeEquals(n1, n2);
	}

	private EqualsVisitor() {
		// hide constructor
	}

	private <T extends Node> boolean nodesEquals(final List<T> nodes1, final List<T> nodes2) {
		if (nodes1 == null) {
			if (nodes2 == null) {
				return true;
			}
			return false;
		} else if (nodes2 == null) {
			return false;
		}
		if (nodes1.size() != nodes2.size()) {
			return false;
		}
		for (int i = 0; i < nodes1.size(); i++) {
			if (!nodeEquals(nodes1.get(i), nodes2.get(i))) {
				return false;
			}
		}
		return true;
	}

	private <T extends Node> boolean nodeEquals(final T n1, final T n2) {
		if (n1 == n2) {
			return true;
		}
		if (n1 == null) {
			if (n2 == null) {
				return true;
			}
			return false;
		} else if (n2 == null) {
			return false;
		}
		if (n1.getClass() != n2.getClass()) {
			return false;
		}
		return n1.accept(this, n2).booleanValue();
	}

	private boolean objEquals(final Object n1, final Object n2) {
		if (n1 == n2) {
			return true;
		}
		if (n1 == null) {
			if (n2 == null) {
				return true;
			}
			return false;
		} else if (n2 == null) {
			return false;
		}
		return n1.equals(n2);
	}

	@Override public Boolean visit(final CompilationUnit n1, final Node arg) {
		final CompilationUnit n2 = (CompilationUnit) arg;

		if (!nodeEquals(n1.getPackage(), n2.getPackage())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getImports(), n2.getImports())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypes(), n2.getTypes())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getComments(), n2.getComments())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final PackageDeclaration n1, final Node arg) {
		final PackageDeclaration n2 = (PackageDeclaration) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ImportDeclaration n1, final Node arg) {
		final ImportDeclaration n2 = (ImportDeclaration) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final TypeParameter n1, final Node arg) {
		final TypeParameter n2 = (TypeParameter) arg;

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeBound(), n2.getTypeBound())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final LineComment n1, final Node arg) {
		final LineComment n2 = (LineComment) arg;

		if (!objEquals(n1.getContent(), n2.getContent())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final BlockComment n1, final Node arg) {
		final BlockComment n2 = (BlockComment) arg;

		if (!objEquals(n1.getContent(), n2.getContent())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ClassOrInterfaceDeclaration n1, final Node arg) {
		final ClassOrInterfaceDeclaration n2 = (ClassOrInterfaceDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (n1.isInterface() != n2.isInterface()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeParameters(), n2.getTypeParameters())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getExtends(), n2.getExtends())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getImplements(), n2.getImplements())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getMembers(), n2.getMembers())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final EnumDeclaration n1, final Node arg) {
		final EnumDeclaration n2 = (EnumDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getImplements(), n2.getImplements())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getEntries(), n2.getEntries())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getMembers(), n2.getMembers())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final EmptyTypeDeclaration n1, final Node arg) {
		return Boolean.TRUE;
	}

	@Override public Boolean visit(final EnumConstantDeclaration n1, final Node arg) {
		final EnumConstantDeclaration n2 = (EnumConstantDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getArgs(), n2.getArgs())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getClassBody(), n2.getClassBody())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final AnnotationDeclaration n1, final Node arg) {
		final AnnotationDeclaration n2 = (AnnotationDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getMembers(), n2.getMembers())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final AnnotationMemberDeclaration n1, final Node arg) {
		final AnnotationMemberDeclaration n2 = (AnnotationMemberDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getDefaultValue(), n2.getDefaultValue())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final FieldDeclaration n1, final Node arg) {
		final FieldDeclaration n2 = (FieldDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getVariables(), n2.getVariables())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final VariableDeclarator n1, final Node arg) {
		final VariableDeclarator n2 = (VariableDeclarator) arg;

		if (!nodeEquals(n1.getId(), n2.getId())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getInit(), n2.getInit())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final VariableDeclaratorId n1, final Node arg) {
		final VariableDeclaratorId n2 = (VariableDeclaratorId) arg;

		if (n1.getArrayCount() != n2.getArrayCount()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ConstructorDeclaration n1, final Node arg) {
		final ConstructorDeclaration n2 = (ConstructorDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBlock(), n2.getBlock())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getParameters(), n2.getParameters())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getThrows(), n2.getThrows())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeParameters(), n2.getTypeParameters())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final MethodDeclaration n1, final Node arg) {
		final MethodDeclaration n2 = (MethodDeclaration) arg;

		// javadoc are checked at CompilationUnit

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (n1.getArrayCount() != n2.getArrayCount()) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBody(), n2.getBody())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getParameters(), n2.getParameters())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getThrows(), n2.getThrows())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeParameters(), n2.getTypeParameters())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}
	
	@Override public Boolean visit(final Parameter n1, final Node arg) {
		final Parameter n2 = (Parameter) arg;
		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}
		return visit((BaseParameter) n1, arg);
	}
	
	@Override public Boolean visit(MultiTypeParameter n1, Node arg) {
		MultiTypeParameter n2 = (MultiTypeParameter) arg;
		if (n1.getTypes().size() != n2.getTypes().size()) {
			return Boolean.FALSE;
		}
		Iterator<Type> n1types = n1.getTypes().iterator();
		Iterator<Type> n2types = n2.getTypes().iterator();
		while (n1types.hasNext() && n2types.hasNext()) {
			if (!nodeEquals(n1types.next(), n2types.next())) {
				return Boolean.FALSE;
			}
		}
		return visit((BaseParameter) n1, arg);
	}

	protected Boolean visit(final BaseParameter n1, final Node arg) {
		final BaseParameter n2 = (BaseParameter) arg;

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getId(), n2.getId())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}
	
	@Override public Boolean visit(final EmptyMemberDeclaration n1, final Node arg) {
		return Boolean.TRUE;
	}

	@Override public Boolean visit(final InitializerDeclaration n1, final Node arg) {
		final InitializerDeclaration n2 = (InitializerDeclaration) arg;

		if (!nodeEquals(n1.getBlock(), n2.getBlock())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final JavadocComment n1, final Node arg) {
		final JavadocComment n2 = (JavadocComment) arg;

		if (!objEquals(n1.getContent(), n2.getContent())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ClassOrInterfaceType n1, final Node arg) {
		final ClassOrInterfaceType n2 = (ClassOrInterfaceType) arg;

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getScope(), n2.getScope())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeArgs(), n2.getTypeArgs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final PrimitiveType n1, final Node arg) {
		final PrimitiveType n2 = (PrimitiveType) arg;

		if (n1.getType() != n2.getType()) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ReferenceType n1, final Node arg) {
		final ReferenceType n2 = (ReferenceType) arg;

		if (n1.getArrayCount() != n2.getArrayCount()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final VoidType n1, final Node arg) {
		return Boolean.TRUE;
	}

	@Override public Boolean visit(final WildcardType n1, final Node arg) {
		final WildcardType n2 = (WildcardType) arg;

		if (!nodeEquals(n1.getExtends(), n2.getExtends())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getSuper(), n2.getSuper())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ArrayAccessExpr n1, final Node arg) {
		final ArrayAccessExpr n2 = (ArrayAccessExpr) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getIndex(), n2.getIndex())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ArrayCreationExpr n1, final Node arg) {
		final ArrayCreationExpr n2 = (ArrayCreationExpr) arg;

		if (n1.getArrayCount() != n2.getArrayCount()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getInitializer(), n2.getInitializer())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getDimensions(), n2.getDimensions())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ArrayInitializerExpr n1, final Node arg) {
		final ArrayInitializerExpr n2 = (ArrayInitializerExpr) arg;

		if (!nodesEquals(n1.getValues(), n2.getValues())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final AssignExpr n1, final Node arg) {
		final AssignExpr n2 = (AssignExpr) arg;

		if (n1.getOperator() != n2.getOperator()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getTarget(), n2.getTarget())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final BinaryExpr n1, final Node arg) {
		final BinaryExpr n2 = (BinaryExpr) arg;

		if (n1.getOperator() != n2.getOperator()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getLeft(), n2.getLeft())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getRight(), n2.getRight())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final CastExpr n1, final Node arg) {
		final CastExpr n2 = (CastExpr) arg;

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ClassExpr n1, final Node arg) {
		final ClassExpr n2 = (ClassExpr) arg;

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ConditionalExpr n1, final Node arg) {
		final ConditionalExpr n2 = (ConditionalExpr) arg;

		if (!nodeEquals(n1.getCondition(), n2.getCondition())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getThenExpr(), n2.getThenExpr())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getElseExpr(), n2.getElseExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final EnclosedExpr n1, final Node arg) {
		final EnclosedExpr n2 = (EnclosedExpr) arg;

		if (!nodeEquals(n1.getInner(), n2.getInner())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final FieldAccessExpr n1, final Node arg) {
		final FieldAccessExpr n2 = (FieldAccessExpr) arg;

		if (!nodeEquals(n1.getScope(), n2.getScope())) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getField(), n2.getField())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeArgs(), n2.getTypeArgs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final InstanceOfExpr n1, final Node arg) {
		final InstanceOfExpr n2 = (InstanceOfExpr) arg;

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final StringLiteralExpr n1, final Node arg) {
		final StringLiteralExpr n2 = (StringLiteralExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final IntegerLiteralExpr n1, final Node arg) {
		final IntegerLiteralExpr n2 = (IntegerLiteralExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final LongLiteralExpr n1, final Node arg) {
		final LongLiteralExpr n2 = (LongLiteralExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final IntegerLiteralMinValueExpr n1, final Node arg) {
		final IntegerLiteralMinValueExpr n2 = (IntegerLiteralMinValueExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final LongLiteralMinValueExpr n1, final Node arg) {
		final LongLiteralMinValueExpr n2 = (LongLiteralMinValueExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final CharLiteralExpr n1, final Node arg) {
		final CharLiteralExpr n2 = (CharLiteralExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final DoubleLiteralExpr n1, final Node arg) {
		final DoubleLiteralExpr n2 = (DoubleLiteralExpr) arg;

		if (!objEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final BooleanLiteralExpr n1, final Node arg) {
		final BooleanLiteralExpr n2 = (BooleanLiteralExpr) arg;

		if (n1.getValue() != n2.getValue()) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final NullLiteralExpr n1, final Node arg) {
		return Boolean.TRUE;
	}

	@Override public Boolean visit(final MethodCallExpr n1, final Node arg) {
		final MethodCallExpr n2 = (MethodCallExpr) arg;

		if (!nodeEquals(n1.getScope(), n2.getScope())) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getArgs(), n2.getArgs())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeArgs(), n2.getTypeArgs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final NameExpr n1, final Node arg) {
		final NameExpr n2 = (NameExpr) arg;

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ObjectCreationExpr n1, final Node arg) {
		final ObjectCreationExpr n2 = (ObjectCreationExpr) arg;

		if (!nodeEquals(n1.getScope(), n2.getScope())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnonymousClassBody(), n2.getAnonymousClassBody())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getArgs(), n2.getArgs())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeArgs(), n2.getTypeArgs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final QualifiedNameExpr n1, final Node arg) {
		final QualifiedNameExpr n2 = (QualifiedNameExpr) arg;

		if (!nodeEquals(n1.getQualifier(), n2.getQualifier())) {
			return Boolean.FALSE;
		}

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ThisExpr n1, final Node arg) {
		final ThisExpr n2 = (ThisExpr) arg;

		if (!nodeEquals(n1.getClassExpr(), n2.getClassExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final SuperExpr n1, final Node arg) {
		final SuperExpr n2 = (SuperExpr) arg;

		if (!nodeEquals(n1.getClassExpr(), n2.getClassExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final UnaryExpr n1, final Node arg) {
		final UnaryExpr n2 = (UnaryExpr) arg;

		if (n1.getOperator() != n2.getOperator()) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final VariableDeclarationExpr n1, final Node arg) {
		final VariableDeclarationExpr n2 = (VariableDeclarationExpr) arg;

		if (n1.getModifiers() != n2.getModifiers()) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getAnnotations(), n2.getAnnotations())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getType(), n2.getType())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getVars(), n2.getVars())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final MarkerAnnotationExpr n1, final Node arg) {
		final MarkerAnnotationExpr n2 = (MarkerAnnotationExpr) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final SingleMemberAnnotationExpr n1, final Node arg) {
		final SingleMemberAnnotationExpr n2 = (SingleMemberAnnotationExpr) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getMemberValue(), n2.getMemberValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final NormalAnnotationExpr n1, final Node arg) {
		final NormalAnnotationExpr n2 = (NormalAnnotationExpr) arg;

		if (!nodeEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getPairs(), n2.getPairs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final MemberValuePair n1, final Node arg) {
		final MemberValuePair n2 = (MemberValuePair) arg;

		if (!objEquals(n1.getName(), n2.getName())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getValue(), n2.getValue())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ExplicitConstructorInvocationStmt n1, final Node arg) {
		final ExplicitConstructorInvocationStmt n2 = (ExplicitConstructorInvocationStmt) arg;

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getArgs(), n2.getArgs())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getTypeArgs(), n2.getTypeArgs())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final TypeDeclarationStmt n1, final Node arg) {
		final TypeDeclarationStmt n2 = (TypeDeclarationStmt) arg;

		if (!nodeEquals(n1.getTypeDeclaration(), n2.getTypeDeclaration())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final AssertStmt n1, final Node arg) {
		final AssertStmt n2 = (AssertStmt) arg;

		if (!nodeEquals(n1.getCheck(), n2.getCheck())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getMessage(), n2.getMessage())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final BlockStmt n1, final Node arg) {
		final BlockStmt n2 = (BlockStmt) arg;

		if (!nodesEquals(n1.getStmts(), n2.getStmts())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final LabeledStmt n1, final Node arg) {
		final LabeledStmt n2 = (LabeledStmt) arg;

		if (!nodeEquals(n1.getStmt(), n2.getStmt())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final EmptyStmt n1, final Node arg) {
		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ExpressionStmt n1, final Node arg) {
		final ExpressionStmt n2 = (ExpressionStmt) arg;

		if (!nodeEquals(n1.getExpression(), n2.getExpression())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final SwitchStmt n1, final Node arg) {
		final SwitchStmt n2 = (SwitchStmt) arg;

		if (!nodeEquals(n1.getSelector(), n2.getSelector())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getEntries(), n2.getEntries())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final SwitchEntryStmt n1, final Node arg) {
		final SwitchEntryStmt n2 = (SwitchEntryStmt) arg;

		if (!nodeEquals(n1.getLabel(), n2.getLabel())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getStmts(), n2.getStmts())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final BreakStmt n1, final Node arg) {
		final BreakStmt n2 = (BreakStmt) arg;

		if (!objEquals(n1.getId(), n2.getId())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ReturnStmt n1, final Node arg) {
		final ReturnStmt n2 = (ReturnStmt) arg;

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final IfStmt n1, final Node arg) {
		final IfStmt n2 = (IfStmt) arg;

		if (!nodeEquals(n1.getCondition(), n2.getCondition())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getThenStmt(), n2.getThenStmt())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getElseStmt(), n2.getElseStmt())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final WhileStmt n1, final Node arg) {
		final WhileStmt n2 = (WhileStmt) arg;

		if (!nodeEquals(n1.getCondition(), n2.getCondition())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBody(), n2.getBody())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ContinueStmt n1, final Node arg) {
		final ContinueStmt n2 = (ContinueStmt) arg;

		if (!objEquals(n1.getId(), n2.getId())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final DoStmt n1, final Node arg) {
		final DoStmt n2 = (DoStmt) arg;

		if (!nodeEquals(n1.getBody(), n2.getBody())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getCondition(), n2.getCondition())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ForeachStmt n1, final Node arg) {
		final ForeachStmt n2 = (ForeachStmt) arg;

		if (!nodeEquals(n1.getVariable(), n2.getVariable())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getIterable(), n2.getIterable())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBody(), n2.getBody())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ForStmt n1, final Node arg) {
		final ForStmt n2 = (ForStmt) arg;

		if (!nodesEquals(n1.getInit(), n2.getInit())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getCompare(), n2.getCompare())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getUpdate(), n2.getUpdate())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBody(), n2.getBody())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final ThrowStmt n1, final Node arg) {
		final ThrowStmt n2 = (ThrowStmt) arg;

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final SynchronizedStmt n1, final Node arg) {
		final SynchronizedStmt n2 = (SynchronizedStmt) arg;

		if (!nodeEquals(n1.getExpr(), n2.getExpr())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getBlock(), n2.getBlock())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final TryStmt n1, final Node arg) {
		final TryStmt n2 = (TryStmt) arg;

		if (!nodeEquals(n1.getTryBlock(), n2.getTryBlock())) {
			return Boolean.FALSE;
		}

		if (!nodesEquals(n1.getCatchs(), n2.getCatchs())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getFinallyBlock(), n2.getFinallyBlock())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

	@Override public Boolean visit(final CatchClause n1, final Node arg) {
		final CatchClause n2 = (CatchClause) arg;

		if (!nodeEquals(n1.getExcept(), n2.getExcept())) {
			return Boolean.FALSE;
		}

		if (!nodeEquals(n1.getCatchBlock(), n2.getCatchBlock())) {
			return Boolean.FALSE;
		}

		return Boolean.TRUE;
	}

}
