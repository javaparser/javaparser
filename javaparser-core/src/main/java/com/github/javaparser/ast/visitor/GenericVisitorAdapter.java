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
 
package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EmptyMemberDeclaration;
import com.github.javaparser.ast.body.EmptyTypeDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.IntegerLiteralMinValueExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralMinValueExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.QualifiedNameExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithArrays;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.TypeDeclarationStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class GenericVisitorAdapter<R, A> implements GenericVisitor<R, A> {

	private R visitArraysAnnotations(NodeWithArrays<?> n, A arg) {
		for(List<AnnotationExpr> aux: n.getArraysAnnotationsList()) {
			if (aux != null) {
				for (AnnotationExpr annotation : aux) {
					R result = annotation.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final AnnotationDeclaration n, final A arg) {
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembersList() != null) {
            for (final BodyDeclaration<?> member : n.getMembersList()) {
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		{
			R result = visitArraysAnnotations(n, arg);
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
		if (n.getDimensionsList() != null) {
			for (final Expression dim : n.getDimensionsList()) {
				{
					R result = dim.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getInitializer() != null) {
			R result = n.getInitializer().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final ArrayInitializerExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getValuesList() != null) {
			for (final Expression expr : n.getValuesList()) {
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
		visitComment(n, arg);
		{
			R result = n.getCheck().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getMsg() != null) {
			{
				R result = n.getMsg().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		return null;
	}

	@Override
	public R visit(final AssignExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getStmtsList() != null) {
			for (final Statement s : n.getStmtsList()) {
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final BreakStmt n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final CastExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		{
			R result = n.getParam().accept(this, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final ClassExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParameterList() != null) {
			for (final TypeParameter t : n.getTypeParameterList()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getExtendsList() != null) {
			for (final ClassOrInterfaceType c : n.getExtendsList()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}

		if (n.getImplementsList() != null) {
			for (final ClassOrInterfaceType c : n.getImplementsList()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembersList() != null) {
            for (final BodyDeclaration<?> member : n.getMembersList()) {
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
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
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
		visitComment(n, arg);
		if (n.getPackage() != null) {
			{
				R result = n.getPackage().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getImportsList() != null) {
			for (final ImportDeclaration i : n.getImportsList()) {
				{
					R result = i.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypesList() != null) {
            for (final TypeDeclaration<?> typeDeclaration : n.getTypesList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParameterList() != null) {
			for (final TypeParameter t : n.getTypeParameterList()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getParametersList() != null) {
			for (final Parameter p : n.getParametersList()) {
				{
					R result = p.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getThrowsList() != null) {
			for (final ReferenceType name : n.getThrowsList()) {
				{
					R result = name.accept(this, arg);
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
	public R visit(final ContinueStmt n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final DoStmt n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final EmptyMemberDeclaration n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final EmptyStmt n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final EmptyTypeDeclaration n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final EnclosedExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getClassBodyList() != null) {
            for (final BodyDeclaration<?> member : n.getClassBodyList()) {
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getImplementsList() != null) {
			for (final ClassOrInterfaceType c : n.getImplementsList()) {
				{
					R result = c.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getEntriesList() != null) {
			for (final EnumConstantDeclaration e : n.getEntriesList()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getMembersList() != null) {
            for (final BodyDeclaration<?> member : n.getMembersList()) {
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
		visitComment(n, arg);
		if (!n.isThis() && n.getExpr() != null) {
			{
				R result = n.getExpr().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
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
		visitComment(n, arg);
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final FieldAccessExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
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
		for (final VariableDeclarator var : n.getVariablesList()) {
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
		visitComment(n, arg);
		{
			R result = n.getVar().accept(this, arg);
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
		visitComment(n, arg);
		if (n.getInitList() != null) {
			for (final Expression e : n.getInitList()) {
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
		if (n.getUpdateList() != null) {
			for (final Expression e : n.getUpdateList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final IntegerLiteralMinValueExpr n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final JavadocComment n, final A arg) {
		return null;
	}

	@Override
	public R visit(final LabeledStmt n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final LongLiteralMinValueExpr n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final MarkerAnnotationExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				{
					R result = t.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
				{
					R result = a.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getTypeParametersList() != null) {
			for (final TypeParameter t : n.getTypeParametersList()) {
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
		if (n.getParametersList() != null) {
			for (final Parameter p : n.getParametersList()) {
				{
					R result = p.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getThrowsList() != null) {
			for (final ReferenceType name : n.getThrowsList()) {
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final NormalAnnotationExpr n, final A arg) {
		visitComment(n, arg);
		{
			R result = n.getName().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getPairsList() != null) {
			for (final MemberValuePair m : n.getPairsList()) {
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final ObjectCreationExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getScope() != null) {
			{
				R result = n.getScope().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
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
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				{
					R result = e.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		if (n.getAnonymousClassBodyList() != null) {
            for (final BodyDeclaration<?> member : n.getAnonymousClassBodyList()) {
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
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
		visitComment(n, arg);
		if (n.getAnnotationsList() != null) {
			for (final AnnotationExpr a : n.getAnnotationsList()) {
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
	public R visit(final PrimitiveType n, final A arg) {
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final QualifiedNameExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		{
			R result = visitArraysAnnotations(n, arg);
			if (result != null) {
				return result;
			}
		}
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
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
    public R visit(final IntersectionType n, final A arg) {
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
        {
            for (ReferenceType element : n.getElementsList()) {
                R result = element.accept(this, arg);
                if (result != null) {
                    return result;
                }
            }
        }
        return null;
    }

    @Override
    public R visit(final UnionType n, final A arg) {
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
        {
            for (ReferenceType element : n.getElementsList()) {
                R result = element.accept(this, arg);
                if (result != null) {
                    return result;
                }
            }
        }
        return null;
    }

	@Override
	public R visit(final ReturnStmt n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final SuperExpr n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getLabel() != null) {
			{
				R result = n.getLabel().accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getStmtsList() != null) {
			for (final Statement s : n.getStmtsList()) {
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
		visitComment(n, arg);
		{
			R result = n.getSelector().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getEntriesList() != null) {
			for (final SwitchEntryStmt e : n.getEntriesList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getResourcesList() != null) {
			for (final VariableDeclarationExpr v : n.getResourcesList()) {
				{
					R result = v.accept(this, arg);
					if (result != null) {
						return result;
					}
				}
			}
		}
		{
			R result = n.getTryBlock().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		if (n.getCatchsList() != null) {
			for (final CatchClause c : n.getCatchsList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		if (n.getTypeBoundList() != null) {
			for (final ClassOrInterfaceType c : n.getTypeBoundList()) {
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
		visitComment(n, arg);
		{
			R result = n.getExpr().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final UnknownType n, final A arg) {
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final VariableDeclarationExpr n, final A arg) {
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
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
		for (final VariableDeclarator v : n.getVarsList()) {
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
		visitComment(n, arg);
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
		visitComment(n, arg);
		return null;
	}

	@Override
	public R visit(final VoidType n, final A arg) {
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
	}

	@Override
	public R visit(final WhileStmt n, final A arg) {
		visitComment(n, arg);
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
		visitComment(n, arg);
		for (final AnnotationExpr a : n.getAnnotationsList()) {
			R result = a.accept(this, arg);
			if (result != null) {
				return result;
			}
		}
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
    public R visit(LambdaExpr n, A arg) {
		visitComment(n, arg);
		if (n.getParametersList() != null) {
			for (final Parameter a : n.getParametersList()) {
				R result = a.accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getBody() != null) {
			R result = n.getBody().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
    }

    @Override
    public R visit(MethodReferenceExpr n, A arg){
		visitComment(n, arg);
		if (n.getTypeArguments().getTypeArgumentsList() != null) {
			for (final Type t : n.getTypeArguments().getTypeArgumentsList()) {
				R result = t.accept(this, arg);
				if (result != null) {
					return result;
				}
			}
		}
		if (n.getScope() != null) {
			R result = n.getScope().accept(this, arg);
			if (result != null) {
				return result;
			}
		}
		return null;
    }

    @Override
    public R visit(TypeExpr n, A arg){
		visitComment(n, arg);
		if (n.getType() != null) {
			R result = n.getType().accept(this, arg);
			if (result != null) {
				return result;
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

	private void visitComment(Node n, A arg) {
		if(n.getComment()!=null){
			Comment result = (Comment) n.getComment().accept(this, arg);
			if(result!=null){
				n.setComment(result);
			}
		}
	}
}
