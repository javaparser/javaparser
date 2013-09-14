/*
 * Copyright (C) 2008 Júlio Vilmar Gesser.
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
 * Created on 09/06/2008
 */
package japa.parser.ast.visitor;

import japa.parser.ast.BlockComment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
import japa.parser.ast.body.BodyDeclaration;
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
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.AnnotationExpr;
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
import japa.parser.ast.expr.Expression;
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
import japa.parser.ast.stmt.Statement;
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

/**
 * @author Julio Vilmar Gesser
 */
public abstract class GenericVisitorAdapter<R, A> implements
		GenericVisitor<R, A> {

	@Override
	public R visit(final AnnotationDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembers() != null) {
			for (final BodyDeclaration member : n.getMembers()) {
				{
					R result = member.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final AnnotationMemberDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getDefaultValue() != null) {
			{
				R result = n.getDefaultValue().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ArrayAccessExpr n, final A arg) {
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getIndex().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ArrayCreationExpr n, final A arg) {
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getDimensions() != null) {
			for (final Expression dim : n.getDimensions()) {
				{
					R result = dim.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		} else {
			{
				R result = n.getInitializer().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ArrayInitializerExpr n, final A arg) {
		if (n.getValues() != null) {
			for (final Expression expr : n.getValues()) {
				{
					R result = expr.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final AssertStmt n, final A arg) {
		{
			R result = n.getCheck().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getMessage() != null) {
			{
				R result = n.getMessage().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final AssignExpr n, final A arg) {
		{
			R result = n.getTarget().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getValue().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final BinaryExpr n, final A arg) {
		{
			R result = n.getLeft().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getRight().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final BlockStmt n, final A arg) {
		if (n.getStmts() != null) {
			for (final Statement s : n.getStmts()) {
				{
					R result = s.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;

	}

	@Override
	public R visit(final BooleanLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final BreakStmt n, final A arg) {
		return null;
	}

	@Override
	public R visit(final CastExpr n, final A arg) {
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final CatchClause n, final A arg) {
		{
			R result = n.getExcept().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getCatchBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;

	}

	@Override
	public R visit(final CharLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final ClassExpr n, final A arg) {
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ClassOrInterfaceDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParameters() != null) {
			for (final TypeParameter t : n.getTypeParameters()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getExtends() != null) {
			for (final ClassOrInterfaceType c : n.getExtends()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}

		if (n.getImplements() != null) {
			for (final ClassOrInterfaceType c : n.getImplements()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembers() != null) {
			for (final BodyDeclaration member : n.getMembers()) {
				{
					R result = member.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ClassOrInterfaceType n, final A arg) {
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgs() != null) {
			for (final Type t : n.getTypeArgs()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final CompilationUnit n, final A arg) {
		if (n.getPackage() != null) {
			{
				R result = n.getPackage().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getImports() != null) {
			for (final ImportDeclaration i : n.getImports()) {
				{
					R result = i.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypes() != null) {
			for (final TypeDeclaration typeDeclaration : n.getTypes()) {
				{
					R result = typeDeclaration.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ConditionalExpr n, final A arg) {
		{
			R result = n.getCondition().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getThenExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getElseExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ConstructorDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParameters() != null) {
			for (final TypeParameter t : n.getTypeParameters()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getParameters() != null) {
			for (final Parameter p : n.getParameters()) {
				{
					R result = p.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getThrows() != null) {
			for (final NameExpr name : n.getThrows()) {
				{
					R result = name.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ContinueStmt n, final A arg) {
		return null;
	}

	@Override
	public R visit(final DoStmt n, final A arg) {
		{
			R result = n.getBody().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getCondition().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final DoubleLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final EmptyMemberDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final EmptyStmt n, final A arg) {
		return null;
	}

	@Override
	public R visit(final EmptyTypeDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final EnclosedExpr n, final A arg) {
		{
			R result = n.getInner().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final EnumConstantDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgs() != null) {
			for (final Expression e : n.getArgs()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getClassBody() != null) {
			for (final BodyDeclaration member : n.getClassBody()) {
				{
					R result = member.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final EnumDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getImplements() != null) {
			for (final ClassOrInterfaceType c : n.getImplements()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getEntries() != null) {
			for (final EnumConstantDeclaration e : n.getEntries()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembers() != null) {
			for (final BodyDeclaration member : n.getMembers()) {
				{
					R result = member.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ExplicitConstructorInvocationStmt n, final A arg) {
		if (!n.isThis()) {
			if (n.getExpr() != null) {
				{
					R result = n.getExpr().accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeArgs() != null) {
			for (final Type t : n.getTypeArgs()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgs() != null) {
			for (final Expression e : n.getArgs()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ExpressionStmt n, final A arg) {
		{
			R result = n.getExpression().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final FieldAccessExpr n, final A arg) {
		{
			R result = n.getScope().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final FieldDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		for (final VariableDeclarator var : n.getVariables()) {
			{
				R result = var.accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ForeachStmt n, final A arg) {
		{
			R result = n.getVariable().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getIterable().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getBody().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ForStmt n, final A arg) {
		if (n.getInit() != null) {
			for (final Expression e : n.getInit()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getCompare() != null) {
			{
				R result = n.getCompare().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getUpdate() != null) {
			for (final Expression e : n.getUpdate()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getBody().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final IfStmt n, final A arg) {
		{
			R result = n.getCondition().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getThenStmt().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getElseStmt() != null) {
			{
				R result = n.getElseStmt().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ImportDeclaration n, final A arg) {
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final InitializerDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		{
			R result = n.getBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final InstanceOfExpr n, final A arg) {
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final IntegerLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final IntegerLiteralMinValueExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final JavadocComment n, final A arg) {
		return null;
	}

	@Override
	public R visit(final LabeledStmt n, final A arg) {
		{
			R result = n.getStmt().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final LongLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final LongLiteralMinValueExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final MarkerAnnotationExpr n, final A arg) {
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final MemberValuePair n, final A arg) {
		{
			R result = n.getValue().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final MethodCallExpr n, final A arg) {
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgs() != null) {
			for (final Type t : n.getTypeArgs()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgs() != null) {
			for (final Expression e : n.getArgs()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final MethodDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			{
				R result = n.getJavaDoc().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParameters() != null) {
			for (final TypeParameter t : n.getTypeParameters()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getParameters() != null) {
			for (final Parameter p : n.getParameters()) {
				{
					R result = p.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getThrows() != null) {
			for (final NameExpr name : n.getThrows()) {
				{
					R result = name.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getBody() != null) {
			{
				R result = n.getBody().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final NameExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final NormalAnnotationExpr n, final A arg) {
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getPairs() != null) {
			for (final MemberValuePair m : n.getPairs()) {
				{
					R result = m.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final NullLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final ObjectCreationExpr n, final A arg) {
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgs() != null) {
			for (final Type t : n.getTypeArgs()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getArgs() != null) {
			for (final Expression e : n.getArgs()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getAnonymousClassBody() != null) {
			for (final BodyDeclaration member : n.getAnonymousClassBody()) {
				{
					R result = member.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final PackageDeclaration n, final A arg) {
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final Parameter n, final A arg) {
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getId().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}
	
	@Override
	public R visit(final MultiTypeParameter n, final A arg) {
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			for (final Type type : n.getTypes()) {
				R result = type.accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		{
			R result = n.getId().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final PrimitiveType n, final A arg) {
		return null;
	}

	@Override
	public R visit(final QualifiedNameExpr n, final A arg) {
		{
			R result = n.getQualifier().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ReferenceType n, final A arg) {
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ReturnStmt n, final A arg) {
		if (n.getExpr() != null) {
			{
				R result = n.getExpr().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final SingleMemberAnnotationExpr n, final A arg) {
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getMemberValue().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final StringLiteralExpr n, final A arg) {
		return null;
	}

	@Override
	public R visit(final SuperExpr n, final A arg) {
		if (n.getClassExpr() != null) {
			{
				R result = n.getClassExpr().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final SwitchEntryStmt n, final A arg) {
		if (n.getLabel() != null) {
			{
				R result = n.getLabel().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getStmts() != null) {
			for (final Statement s : n.getStmts()) {
				{
					R result = s.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final SwitchStmt n, final A arg) {
		{
			R result = n.getSelector().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getEntries() != null) {
			for (final SwitchEntryStmt e : n.getEntries()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;

	}

	@Override
	public R visit(final SynchronizedStmt n, final A arg) {
		{
			if (n.getExpr() != null) {
			    R result = n.getExpr().accept(this, arg);
			    if (result != null) {
				    return result;
			    }
			}
		}
		{
			R result = n.getBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ThisExpr n, final A arg) {
		if (n.getClassExpr() != null) {
			{
				R result = n.getClassExpr().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final ThrowStmt n, final A arg) {
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final TryStmt n, final A arg) {
		{
			R result = n.getTryBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getCatchs() != null) {
			for (final CatchClause c : n.getCatchs()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getFinallyBlock() != null) {
			{
				R result = n.getFinallyBlock().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final TypeDeclarationStmt n, final A arg) {
		{
			R result = n.getTypeDeclaration().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final TypeParameter n, final A arg) {
		if (n.getTypeBound() != null) {
			for (final ClassOrInterfaceType c : n.getTypeBound()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final UnaryExpr n, final A arg) {
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final VariableDeclarationExpr n, final A arg) {
		if (n.getAnnotations() != null) {
			for (final AnnotationExpr a : n.getAnnotations()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		for (final VariableDeclarator v : n.getVars()) {
			{
				R result = v.accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final VariableDeclarator n, final A arg) {
		{
			R result = n.getId().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getInit() != null) {
			{
				R result = n.getInit().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final VariableDeclaratorId n, final A arg) {
		return null;
	}

	@Override
	public R visit(final VoidType n, final A arg) {
		return null;
	}

	@Override
	public R visit(final WhileStmt n, final A arg) {
		{
			R result = n.getCondition().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		{
			R result = n.getBody().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final WildcardType n, final A arg) {
		if (n.getExtends() != null) {
			{
				R result = n.getExtends().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getSuper() != null) {
			{
				R result = n.getSuper().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final BlockComment n, final A arg) {
		return null;
	}

	@Override
	public R visit(final LineComment n, final A arg) {
		return null;
	}

}
