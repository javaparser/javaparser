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
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithArrays;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.ArrayList;
import java.util.List;

/**
 * This visitor adapter can be used to save time when some specific nodes needs
 * to be changed. To do that just extend this class and override the methods
 * from the nodes who needs to be changed, returning the changed node.
 * 
 * @author Julio Vilmar Gesser
 */
public abstract class ModifierVisitorAdapter<A> implements GenericVisitor<Node, A> {

	private void removeNulls(final List<?> list) {
		for (int i = list.size() - 1; i >= 0; i--) {
			if (list.get(i) == null) {
				list.remove(i);
			}
		}
	}

	private void visitArraysAnnotations(NodeWithArrays<?> n, A arg) {
		/* TODO this code always keeps annotations for the same amount of array indexes, since we can't see if
		 the user wants to say "I want no annotations on this array index" or "I don't want this array index anymore"
		  */
		List<List<AnnotationExpr>> resultList = new ArrayList<>();
		for (List<AnnotationExpr> aux : n.getArraysAnnotationsList()) {
			if (aux == null) {
				resultList.add(null);
			} else {
				List<AnnotationExpr> lList = new ArrayList<>();
				for (AnnotationExpr annotation : aux) {
					AnnotationExpr newAnnotationExpr = (AnnotationExpr) annotation.accept(this, arg);
					if (newAnnotationExpr != null) {
						lList.add(newAnnotationExpr);
					}
				}
				resultList.add(lList);
			}
		}
		n.setArraysAnnotationsList(resultList);
	}

	@Override public Node visit(final AnnotationDeclaration n, final A arg) {
		visitAnnotations(n, arg);
		visitComment(n, arg);
        final List<BodyDeclaration<?>> membersList = n.getMembersList();
		if (membersList != null) {
			for (int i = 0; i < membersList.size(); i++) {
                membersList.set(i, (BodyDeclaration<?>) membersList.get(i).accept(this, arg));
			}
			removeNulls(membersList);
		}
		return n;
	}

	private void visitAnnotations(NodeWithAnnotations<?> n, A arg) {
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
	}

	@Override public Node visit(final AnnotationMemberDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		n.setType((Type) n.getType().accept(this, arg));
		if (n.getDefaultValue() != null) {
			n.setDefaultValue((Expression) n.getDefaultValue().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ArrayAccessExpr n, final A arg) {
		visitComment(n, arg);
		n.setName((Expression) n.getName().accept(this, arg));
		n.setIndex((Expression) n.getIndex().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ArrayCreationExpr n, final A arg) {
		visitComment(n, arg);
		n.setType((Type) n.getType().accept(this, arg));
		if (n.getDimensionsList() != null) {
			final List<Expression> dimensionsList = n.getDimensionsList();
			if (dimensionsList != null) {
				for (int i = 0; i < dimensionsList.size(); i++) {
					dimensionsList.set(i, (Expression) dimensionsList.get(i).accept(this, arg));
				}
				removeNulls(dimensionsList);
			}
		}
		visitArraysAnnotations(n, arg);

		if (n.getInitializer() != null) {
			n.setInitializer((ArrayInitializerExpr) n.getInitializer().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ArrayInitializerExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getValuesList() != null) {
			final List<Expression> valuesList = n.getValuesList();
			if (valuesList != null) {
				for (int i = 0; i < valuesList.size(); i++) {
					valuesList.set(i, (Expression) valuesList.get(i).accept(this, arg));
				}
				removeNulls(valuesList);
			}
		}
		return n;
	}

	@Override public Node visit(final AssertStmt n, final A arg) {
		visitComment(n, arg);
		n.setCheck((Expression) n.getCheck().accept(this, arg));
		if (n.getMsg() != null) {
			n.setMsg((Expression) n.getMsg().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final AssignExpr n, final A arg) {
		visitComment(n, arg);
		final Expression target = (Expression) n.getTarget().accept(this, arg);
		if (target == null) {
			return null;
		}
        n.setTarget(target);

		final Expression value = (Expression) n.getValue().accept(this, arg);
		if (value == null) {
			return null;
		}
		n.setValue(value);

		return n;
	}

	@Override public Node visit(final BinaryExpr n, final A arg) {
		visitComment(n, arg);
		final Expression left = (Expression) n.getLeft().accept(this, arg);
		final Expression right = (Expression) n.getRight().accept(this, arg);
		if (left == null) {
			return right;
		}
		if (right == null) {
			return left;
		}
		n.setLeft(left);
		n.setRight(right);
		return n;
	}

	@Override public Node visit(final BlockStmt n, final A arg) {
		visitComment(n, arg);
		final List<Statement> stmtsList = n.getStmtsList();
		if (stmtsList != null) {
			for (int i = 0; i < stmtsList.size(); i++) {
				stmtsList.set(i, (Statement) stmtsList.get(i).accept(this, arg));
			}
			removeNulls(stmtsList);
		}
		return n;
	}

	@Override public Node visit(final BooleanLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final BreakStmt n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final CastExpr n, final A arg) {
		visitComment(n, arg);
		final Type type = (Type) n.getType().accept(this, arg);
		final Expression expr = (Expression) n.getExpr().accept(this, arg);
		if (type == null) {
			return expr;
		}
		if (expr == null) {
			return null;
		}
		n.setType(type);
		n.setExpr(expr);
		return n;
	}

	@Override public Node visit(final CatchClause n, final A arg) {
		visitComment(n, arg);
		n.setParam((Parameter)n.getParam().accept(this, arg));
		n.setCatchBlock((BlockStmt) n.getCatchBlock().accept(this, arg));
		return n;

	}

	@Override public Node visit(final CharLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final ClassExpr n, final A arg) {
		visitComment(n, arg);
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ClassOrInterfaceDeclaration n, final A arg) {
		visitAnnotations(n, arg);
		visitComment(n, arg);
		final List<TypeParameter> typeParametersList = n.getTypeParameterList();
		if (typeParametersList != null) {
			for (int i = 0; i < typeParametersList.size(); i++) {
				typeParametersList.set(i, (TypeParameter) typeParametersList.get(i).accept(this, arg));
			}
			removeNulls(typeParametersList);
		}
		final List<ClassOrInterfaceType> extendsList = n.getExtendsList();
		if (extendsList != null) {
			for (int i = 0; i < extendsList.size(); i++) {
				extendsList.set(i, (ClassOrInterfaceType) extendsList.get(i).accept(this, arg));
			}
			removeNulls(extendsList);
		}
		final List<ClassOrInterfaceType> implementsList = n.getImplementsList();
		if (implementsList != null) {
			for (int i = 0; i < implementsList.size(); i++) {
				implementsList.set(i, (ClassOrInterfaceType) implementsList.get(i).accept(this, arg));
			}
			removeNulls(implementsList);
		}
        final List<BodyDeclaration<?>> membersList = n.getMembersList();
		if (membersList != null) {
			for (int i = 0; i < membersList.size(); i++) {
                membersList.set(i, (BodyDeclaration<?>) membersList.get(i).accept(this, arg));
			}
			removeNulls(membersList);
		}
		return n;
	}

	@Override public Node visit(final ClassOrInterfaceType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		if (n.getScope() != null) {
			n.setScope((ClassOrInterfaceType) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgsList = n.getTypeArgsList();
		if (typeArgsList != null) {
			for (int i = 0; i < typeArgsList.size(); i++) {
				typeArgsList.set(i, (Type) typeArgsList.get(i).accept(this, arg));
			}
			removeNulls(typeArgsList);
		}
		return n;
	}

	@Override public Node visit(final CompilationUnit n, final A arg) {
		visitComment(n, arg);
		if (n.getPackage() != null) {
			n.setPackage((PackageDeclaration) n.getPackage().accept(this, arg));
		}
		final List<ImportDeclaration> importsList = n.getImportsList();
		if (importsList != null) {
			for (int i = 0; i < importsList.size(); i++) {
				importsList.set(i, (ImportDeclaration) importsList.get(i).accept(this, arg));
			}
			removeNulls(importsList);
		}
        final List<TypeDeclaration<?>> types = n.getTypesList();
		if (types != null) {
			for (int i = 0; i < types.size(); i++) {
                types.set(i, (TypeDeclaration<?>) types.get(i).accept(this, arg));
			}
			removeNulls(types);
		}
		return n;
	}

	@Override public Node visit(final ConditionalExpr n, final A arg) {
		visitComment(n, arg);
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		n.setThenExpr((Expression) n.getThenExpr().accept(this, arg));
		n.setElseExpr((Expression) n.getElseExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ConstructorDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		final List<TypeParameter> typeParametersList = n.getTypeParameterList();
		if (typeParametersList != null) {
			for (int i = 0; i < typeParametersList.size(); i++) {
				typeParametersList.set(i, (TypeParameter) typeParametersList.get(i).accept(this, arg));
			}
			removeNulls(typeParametersList);
		}
		final List<Parameter> parametersList = n.getParametersList();
		if (parametersList != null) {
			for (int i = 0; i < parametersList.size(); i++) {
				parametersList.set(i, (Parameter) parametersList.get(i).accept(this, arg));
			}
			removeNulls(parametersList);
		}
		final List<ReferenceType> throwsList = n.getThrowsList();
		if (throwsList != null) {
			for (int i = 0; i < throwsList.size(); i++) {
				throwsList.set(i, (ReferenceType) throwsList.get(i).accept(this, arg));
			}
			removeNulls(throwsList);
		}
		n.setBody((BlockStmt) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ContinueStmt n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final DoStmt n, final A arg) {
		visitComment(n, arg);
		final Statement body = (Statement) n.getBody().accept(this, arg);
		if (body == null) {
			return null;
		}
		n.setBody(body);

		final Expression condition = (Expression) n.getCondition().accept(this, arg);
		if (condition == null) {
			return null;
		}
		n.setCondition(condition);

		return n;
	}

	@Override public Node visit(final DoubleLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final EmptyMemberDeclaration n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final EmptyStmt n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final EmptyTypeDeclaration n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final EnclosedExpr n, final A arg) {
		visitComment(n, arg);
		n.setInner((Expression) n.getInner().accept(this, arg));
		return n;
	}

	@Override public Node visit(final EnumConstantDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		final List<Expression> argsList = n.getArgsList();
		if (argsList != null) {
			for (int i = 0; i < argsList.size(); i++) {
				argsList.set(i, (Expression) argsList.get(i).accept(this, arg));
			}
			removeNulls(argsList);
		}
        final List<BodyDeclaration<?>> classBodyList = n.getClassBodyList();
		if (classBodyList != null) {
			for (int i = 0; i < classBodyList.size(); i++) {
                classBodyList.set(i, (BodyDeclaration<?>) classBodyList.get(i).accept(this, arg));
			}
			removeNulls(classBodyList);
		}
		return n;
	}

	@Override public Node visit(final EnumDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		final List<ClassOrInterfaceType> implementsList = n.getImplementsList();
		if (implementsList != null) {
			for (int i = 0; i < implementsList.size(); i++) {
				implementsList.set(i, (ClassOrInterfaceType) implementsList.get(i).accept(this, arg));
			}
			removeNulls(implementsList);
		}
		final List<EnumConstantDeclaration> entriesList = n.getEntriesList();
		if (entriesList != null) {
			for (int i = 0; i < entriesList.size(); i++) {
				entriesList.set(i, (EnumConstantDeclaration) entriesList.get(i).accept(this, arg));
			}
			removeNulls(entriesList);
		}
        final List<BodyDeclaration<?>> membersList = n.getMembersList();
		if (membersList != null) {
			for (int i = 0; i < membersList.size(); i++) {
                membersList.set(i, (BodyDeclaration<?>) membersList.get(i).accept(this, arg));
			}
			removeNulls(membersList);
		}
		return n;
	}

	@Override public Node visit(final ExplicitConstructorInvocationStmt n, final A arg) {
		visitComment(n, arg);
		if (!n.isThis() && n.getExpr() != null) {
			n.setExpr((Expression) n.getExpr().accept(this, arg));
		}
		final List<Type> typeArgsList = n.getTypeArgsList();
		if (typeArgsList != null) {
			for (int i = 0; i < typeArgsList.size(); i++) {
				typeArgsList.set(i, (Type) typeArgsList.get(i).accept(this, arg));
			}
			removeNulls(typeArgsList);
		}
		final List<Expression> argsList = n.getArgsList();
		if (argsList != null) {
			for (int i = 0; i < argsList.size(); i++) {
				argsList.set(i, (Expression) argsList.get(i).accept(this, arg));
			}
			removeNulls(argsList);
		}
		return n;
	}

	@Override public Node visit(final ExpressionStmt n, final A arg) {
		visitComment(n, arg);
		final Expression expr = (Expression) n.getExpr().accept(this, arg);
		if (expr == null) {
			return null;
		}
		n.setExpr(expr);
		return n;
	}

	@Override public Node visit(final FieldAccessExpr n, final A arg) {
		visitComment(n, arg);
		final Expression scope = (Expression) n.getScope().accept(this, arg);
		if (scope == null) {
			return null;
		}
		n.setScope(scope);
		return n;
	}

	@Override public Node visit(final FieldDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		n.setType((Type) n.getType().accept(this, arg));
		final List<VariableDeclarator> variablesList = n.getVariablesList();
		for (int i = 0; i < variablesList.size(); i++) {
			variablesList.set(i, (VariableDeclarator) variablesList.get(i).accept(this, arg));
		}
		removeNulls(variablesList);
		return n;
	}

	@Override public Node visit(final ForeachStmt n, final A arg) {
		visitComment(n, arg);
		n.setVar((VariableDeclarationExpr) n.getVar().accept(this, arg));
		n.setIterable((Expression) n.getIterable().accept(this, arg));
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ForStmt n, final A arg) {
		visitComment(n, arg);
		final List<Expression> initList = n.getInitList();
		if (initList != null) {
			for (int i = 0; i < initList.size(); i++) {
				initList.set(i, (Expression) initList.get(i).accept(this, arg));
			}
			removeNulls(initList);
		}
		if (n.getCompare() != null) {
			n.setCompare((Expression) n.getCompare().accept(this, arg));
		}
		final List<Expression> updateList = n.getUpdateList();
		if (updateList != null) {
			for (int i = 0; i < updateList.size(); i++) {
				updateList.set(i, (Expression) updateList.get(i).accept(this, arg));
			}
			removeNulls(updateList);
		}
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final IfStmt n, final A arg) {
		visitComment(n, arg);
		final Expression condition = (Expression)
			n.getCondition().accept(this, arg);
		if (condition == null) {
			return null;
		}
		n.setCondition(condition);
		final Statement thenStmt = (Statement) n.getThenStmt().accept(this, arg);
		if (thenStmt == null) {
			// Remove the entire statement if the then-clause was removed.
			// DumpVisitor, used for toString, has no null check for the
			// then-clause.
			return null;
		}
		n.setThenStmt(thenStmt);
		if (n.getElseStmt() != null) {
			n.setElseStmt((Statement) n.getElseStmt().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ImportDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}

	@Override public Node visit(final InitializerDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setBlock((BlockStmt) n.getBlock().accept(this, arg));
		return n;
	}

	@Override public Node visit(final InstanceOfExpr n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

	@Override public Node visit(final IntegerLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final IntegerLiteralMinValueExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final JavadocComment n, final A arg) {
		return n;
	}

	@Override public Node visit(final LabeledStmt n, final A arg) {
		visitComment(n, arg);
		n.setStmt((Statement) n.getStmt().accept(this, arg));
		return n;
	}

	@Override public Node visit(final LongLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final LongLiteralMinValueExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final MarkerAnnotationExpr n, final A arg) {
		visitComment(n, arg);
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}

	@Override public Node visit(final MemberValuePair n, final A arg) {
		visitComment(n, arg);
		n.setValue((Expression) n.getValue().accept(this, arg));
		return n;
	}

	@Override public Node visit(final MethodCallExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getScope() != null) {
			n.setScope((Expression) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgsList = n.getTypeArgsList();
		if (typeArgsList != null) {
			for (int i = 0; i < typeArgsList.size(); i++) {
				typeArgsList.set(i, (Type) typeArgsList.get(i).accept(this, arg));
			}
			removeNulls(typeArgsList);
		}
		final List<Expression> argsList = n.getArgsList();
		if (argsList != null) {
			for (int i = 0; i < argsList.size(); i++) {
				argsList.set(i, (Expression) argsList.get(i).accept(this, arg));
			}
			removeNulls(argsList);
		}
		return n;
	}

	@Override public Node visit(final MethodDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		final List<TypeParameter> typeParametersList = n.getTypeParametersList();
		if (typeParametersList != null) {
			for (int i = 0; i < typeParametersList.size(); i++) {
				typeParametersList.set(i, (TypeParameter) typeParametersList.get(i).accept(this, arg));
			}
			removeNulls(typeParametersList);
		}
		n.setType((Type) n.getType().accept(this, arg));
		final List<Parameter> parametersList = n.getParametersList();
		if (parametersList != null) {
			for (int i = 0; i < parametersList.size(); i++) {
				parametersList.set(i, (Parameter) parametersList.get(i).accept(this, arg));
			}
			removeNulls(parametersList);
		}
		final List<ReferenceType> throwsList = n.getThrowsList();
		if (throwsList != null) {
			for (int i = 0; i < throwsList.size(); i++) {
				throwsList.set(i, (ReferenceType) throwsList.get(i).accept(this, arg));
			}
			removeNulls(throwsList);
		}
		if (n.getBody() != null) {
			n.setBody((BlockStmt) n.getBody().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final NameExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final NormalAnnotationExpr n, final A arg) {
		visitComment(n, arg);
		n.setName((NameExpr) n.getName().accept(this, arg));
		final List<MemberValuePair> pairsList = n.getPairsList();
		if (pairsList != null) {
			for (int i = 0; i < pairsList.size(); i++) {
				pairsList.set(i, (MemberValuePair) pairsList.get(i).accept(this, arg));
			}
			removeNulls(pairsList);
		}
		return n;
	}

	@Override public Node visit(final NullLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final ObjectCreationExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getScope() != null) {
			n.setScope((Expression) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgsList = n.getTypeArgsList();
		if (typeArgsList != null) {
			for (int i = 0; i < typeArgsList.size(); i++) {
				typeArgsList.set(i, (Type) typeArgsList.get(i).accept(this, arg));
			}
			removeNulls(typeArgsList);
		}
		n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
		final List<Expression> argsList = n.getArgsList();
		if (argsList != null) {
			for (int i = 0; i < argsList.size(); i++) {
				argsList.set(i, (Expression) argsList.get(i).accept(this, arg));
			}
			removeNulls(argsList);
		}
        final List<BodyDeclaration<?>> anonymousClassBodyList = n.getAnonymousClassBodyList();
		if (anonymousClassBodyList != null) {
			for (int i = 0; i < anonymousClassBodyList.size(); i++) {
                anonymousClassBodyList.set(i, (BodyDeclaration<?>) anonymousClassBodyList.get(i).accept(this, arg));
			}
			removeNulls(anonymousClassBodyList);
		}
		return n;
	}

	@Override public Node visit(final PackageDeclaration n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}
	
	@Override public Node visit(final Parameter n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		n.setId((VariableDeclaratorId) n.getId().accept(this, arg));
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}
	
	@Override public Node visit(final PrimitiveType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		return n;
	}

	@Override public Node visit(final QualifiedNameExpr n, final A arg) {
		visitComment(n, arg);
		n.setQualifier((NameExpr) n.getQualifier().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ReferenceType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		visitArraysAnnotations(n, arg);
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

    @Override
    public Node visit(final IntersectionType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
        final List<ReferenceType> elementsList = n.getElementsList();
        if (elementsList != null) {
            for (int i = 0; i < elementsList.size(); i++) {
                elementsList.set(i, (ReferenceType) elementsList.get(i).accept(this, arg));
            }
            removeNulls(elementsList);
        }
        return n;
    }

    @Override
    public Node visit(final UnionType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		final List<ReferenceType> elementsList = n.getElementsList();
        if (elementsList != null) {
            for (int i = 0; i < elementsList.size(); i++) {
                elementsList.set(i, (ReferenceType) elementsList.get(i).accept(this, arg));
            }
            removeNulls(elementsList);
        }
        return n;
    }

	@Override public Node visit(final ReturnStmt n, final A arg) {
		visitComment(n, arg);
		if (n.getExpr() != null) {
			n.setExpr((Expression) n.getExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final SingleMemberAnnotationExpr n, final A arg) {
		visitComment(n, arg);
		n.setName((NameExpr) n.getName().accept(this, arg));
		n.setMemberValue((Expression) n.getMemberValue().accept(this, arg));
		return n;
	}

	@Override public Node visit(final StringLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final SuperExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getClassExpr() != null) {
			n.setClassExpr((Expression) n.getClassExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final SwitchEntryStmt n, final A arg) {
		visitComment(n, arg);
		if (n.getLabel() != null) {
			n.setLabel((Expression) n.getLabel().accept(this, arg));
		}
		final List<Statement> stmtsList = n.getStmtsList();
		if (stmtsList != null) {
			for (int i = 0; i < stmtsList.size(); i++) {
				stmtsList.set(i, (Statement) stmtsList.get(i).accept(this, arg));
			}
			removeNulls(stmtsList);
		}
		return n;
	}

	@Override public Node visit(final SwitchStmt n, final A arg) {
		visitComment(n, arg);
		n.setSelector((Expression) n.getSelector().accept(this, arg));
		final List<SwitchEntryStmt> entriesList = n.getEntriesList();
		if (entriesList != null) {
			for (int i = 0; i < entriesList.size(); i++) {
				entriesList.set(i, (SwitchEntryStmt) entriesList.get(i).accept(this, arg));
			}
			removeNulls(entriesList);
		}
		return n;

	}

	@Override public Node visit(final SynchronizedStmt n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		n.setBlock((BlockStmt) n.getBlock().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ThisExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getClassExpr() != null) {
			n.setClassExpr((Expression) n.getClassExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ThrowStmt n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TryStmt n, final A arg) {
		visitComment(n, arg);
		final List<VariableDeclarationExpr> typesList = n.getResourcesList();
		for (int i = 0; i < typesList.size(); i++) {
			n.getResourcesList().set(i,
					(VariableDeclarationExpr) n.getResourcesList().get(i).accept(this, arg));
		}
		n.setTryBlock((BlockStmt) n.getTryBlock().accept(this, arg));
		final List<CatchClause> catchsList = n.getCatchsList();
		if (catchsList != null) {
			for (int i = 0; i < catchsList.size(); i++) {
				catchsList.set(i, (CatchClause) catchsList.get(i).accept(this, arg));
			}
			removeNulls(catchsList);
		}
		if (n.getFinallyBlock() != null) {
			n.setFinallyBlock((BlockStmt) n.getFinallyBlock().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final TypeDeclarationStmt n, final A arg) {
		visitComment(n, arg);
		n.setTypeDeclaration((TypeDeclaration<?>) n.getTypeDeclaration().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TypeParameter n, final A arg) {
		visitComment(n, arg);
		final List<ClassOrInterfaceType> typeBoundList = n.getTypeBoundList();
		if (typeBoundList != null) {
			for (int i = 0; i < typeBoundList.size(); i++) {
				typeBoundList.set(i, (ClassOrInterfaceType) typeBoundList.get(i).accept(this, arg));
			}
			removeNulls(typeBoundList);
		}
		return n;
	}

	@Override public Node visit(final UnaryExpr n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final UnknownType n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final VariableDeclarationExpr n, final A arg) {
		visitComment(n, arg);
		final List<AnnotationExpr> annotationsList = n.getAnnotationsList();
		if (annotationsList != null) {
			for (int i = 0; i < annotationsList.size(); i++) {
				annotationsList.set(i, (AnnotationExpr) annotationsList.get(i).accept(this, arg));
			}
			removeNulls(annotationsList);
		}

		final Type type = (Type) n.getType().accept(this, arg);
		if (type == null) {
			return null;
		}
		n.setType(type);

		final List<VariableDeclarator> varsList = n.getVarsList();
		for (int i = 0; i < varsList.size();) {
			final VariableDeclarator decl = (VariableDeclarator)
				varsList.get(i).accept(this, arg);
			if (decl == null) {
				varsList.remove(i);
			} else {
				varsList.set(i++, decl);
			}
		}
		if (varsList.isEmpty()) {
			return null;
		}

		return n;
	}

	@Override public Node visit(final VariableDeclarator n, final A arg) {
		visitComment(n, arg);
		final VariableDeclaratorId id = (VariableDeclaratorId)
			n.getId().accept(this, arg);
		if (id == null) {
			return null;
		}
		n.setId(id);
		if (n.getInit() != null) {
			n.setInit((Expression) n.getInit().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final VariableDeclaratorId n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final VoidType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		return n;
	}

	@Override public Node visit(final WhileStmt n, final A arg) {
		visitComment(n, arg);
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final WildcardType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		if (n.getExtends() != null) {
			n.setExt((ReferenceType) n.getExtends().accept(this, arg));
		}
		if (n.getSuper() != null) {
			n.setSup((ReferenceType) n.getSuper().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final LambdaExpr n, final A arg) {
		visitComment(n, arg);
		final List<Parameter> parametersList = n.getParametersList();
		for (int i = 0; i < parametersList.size(); i++) {
			parametersList.set(i, (Parameter) parametersList.get(i).accept(this, arg));
		}
		removeNulls(parametersList);
		if (n.getBody() != null) {
			n.setBody((Statement) n.getBody().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final MethodReferenceExpr n, final A arg) {
		visitComment(n, arg);
		final List<Type> typesList = n.getTypeArguments().getTypeArgumentsList();
		for (int i = 0; i < typesList.size(); i++) {
			n.getTypeArguments().getTypeArgumentsList().set(i,
					(Type) n.getTypeArguments().getTypeArgumentsList().get(i).accept(this, arg));
		}
		if (n.getScope() != null) {
			n.setScope((Expression)n.getScope().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final TypeExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getType() != null) {
			n.setType((Type)n.getType().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final BlockComment n, final A arg) {
		return n;
	}

	@Override
	public Node visit(final LineComment n, final A arg) {
		return n;
	}

	private void visitComment(Node n, final A arg) {
		if (n != null && n.getComment() != null) {
			n.setComment((Comment) n.getComment().accept(this, arg));
		}
	}
}
