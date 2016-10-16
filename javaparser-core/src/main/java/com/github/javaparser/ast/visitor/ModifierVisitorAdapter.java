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
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.List;

import static com.github.javaparser.utils.Utils.option;

/**
 * This visitor adapter can be used to save time when some specific nodes needs
 * to be changed. To do that just extend this class and override the methods
 * from the nodes who needs to be changed, returning the changed node.
 * 
 * @author Julio Vilmar Gesser
 */
public class ModifierVisitorAdapter<A> implements GenericVisitor<Node, A> {
    @Override public Node visit(final AnnotationDeclaration n, final A arg) {
		visitAnnotations(n, arg);
		visitComment(n, arg);
        n.setMembers((NodeList<BodyDeclaration<?>>) n.getMembers().accept(this, arg));
		return n;
	}

	private void visitAnnotations(NodeWithAnnotations<?> n, A arg) {
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
	}

	@Override public Node visit(final AnnotationMemberDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
		n.setType((Type) n.getType().accept(this, arg));
        n.setDefaultValue(n.getDefaultValue().flatMap(dv -> option((Expression) dv.accept(this, arg))));
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
		n.setElementType((Type) n.getElementType().accept(this, arg));
        n.setLevels((NodeList<ArrayCreationLevel>)n.getLevels().accept(this, arg));
        n.setInitializer(n.getInitializer().flatMap(dv -> option((ArrayInitializerExpr) dv.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final ArrayInitializerExpr n, final A arg) {
		visitComment(n, arg);
        n.setValues((NodeList<Expression>)n.getValues().accept(this, arg));
		return n;
	}

	@Override public Node visit(final AssertStmt n, final A arg) {
		visitComment(n, arg);
		n.setCheck((Expression) n.getCheck().accept(this, arg));
        n.setMessage(n.getMessage().flatMap(p -> option((Expression) p.accept(this, arg))));
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
		n.setStmts((NodeList<Statement>) n.getStmts().accept(this, arg));
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
		n.setBody((BlockStmt) n.getBody().accept(this, arg));
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
		n.setTypeParameters(modifyList(n.getTypeParameters(), arg));
		n.setExtends(modifyList(n.getExtends(), arg));
		n.setImplements(modifyList(n.getImplements(), arg));
		n.setMembers((NodeList<BodyDeclaration<?>>) n.getMembers().accept(this, arg));
		return n;
	}

    private <N extends Node> NodeList<N> modifyList(NodeList<N> list, A arg) {
        if(list==null){
            return null;
        }
        return (NodeList<N>) list.accept(this, arg);
    }

    @Override public Node visit(final ClassOrInterfaceType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
        n.setScope(n.getScope().flatMap(p -> option((ClassOrInterfaceType) p.accept(this, arg))));
        n.setTypeArguments(n.getTypeArguments().flatMap(p -> option((NodeList<Type<?>>) modifyList(p, arg))));
		return n;
	}

	@Override public Node visit(final CompilationUnit n, final A arg) {
		visitComment(n, arg);
        n.setPackage(n.getPackage().flatMap(p -> option((PackageDeclaration) p.accept(this, arg))));
		n.setImports((NodeList<ImportDeclaration> )n.getImports().accept(this, arg));
		n.setTypes((NodeList<TypeDeclaration<?>> )n.getTypes().accept(this, arg));
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
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
        n.setTypeParameters(modifyList(n.getTypeParameters(), arg));
		n.setParameters((NodeList<Parameter>)n.getParameters().accept(this, arg));
		n.setThrows((NodeList<ReferenceType<?>>)n.getThrows().accept(this, arg));
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
        n.setInner(n.getInner().flatMap(p -> option((Expression) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final EnumConstantDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
        n.setArgs((NodeList<Expression>)n.getArgs().accept(this, arg));
        n.setClassBody((NodeList<BodyDeclaration<?>>)n.getClassBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final EnumDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
		n.setImplements((NodeList<ClassOrInterfaceType>) n.getImplements().accept(this, arg));
        n.setEntries((NodeList<EnumConstantDeclaration>)n.getEntries().accept(this, arg));
        n.setMembers((NodeList<BodyDeclaration<?>>) n.getMembers().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ExplicitConstructorInvocationStmt n, final A arg) {
		visitComment(n, arg);
		if (!n.isThis() && n.getExpr() != null) {
			n.setExpr((Expression) n.getExpr().accept(this, arg));
		}
        n.setTypeArguments(n.getTypeArguments().flatMap(p -> option((NodeList<Type<?>>) modifyList(p, arg))));
        n.setArgs((NodeList<Expression>)n.getArgs().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ExpressionStmt n, final A arg) {
		visitComment(n, arg);
		final Expression expr = (Expression) n.getExpression().accept(this, arg);
		if (expr == null) {
			return null;
		}
		n.setExpression(expr);
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
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
		n.setElementType((Type) n.getElementType().accept(this, arg));
        n.setVariables((NodeList<VariableDeclarator>)n.getVariables().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ForeachStmt n, final A arg) {
		visitComment(n, arg);
		n.setVariable((VariableDeclarationExpr) n.getVariable().accept(this, arg));
		n.setIterable((Expression) n.getIterable().accept(this, arg));
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ForStmt n, final A arg) {
		visitComment(n, arg);
        n.setInit((NodeList<Expression>)n.getInit().accept(this, arg));
		if (n.getCompare() != null) {
			n.setCompare((Expression) n.getCompare().accept(this, arg));
		}
        n.setUpdate((NodeList<Expression>)n.getUpdate().accept(this, arg));
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
        n.setElseStmt(n.getElseStmt().flatMap(p -> option((Statement) p.accept(this, arg))));
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
		n.setType((ReferenceType<?>) n.getType().accept(this, arg));
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
        n.setScope(n.getScope().flatMap(p -> option((Expression) p.accept(this, arg))));
        n.setTypeArguments(n.getTypeArguments().flatMap(p -> option((NodeList<Type<?>>) modifyList(p, arg))));
        n.setArgs((NodeList<Expression>)n.getArgs().accept(this, arg));
		return n;
	}

	@Override public Node visit(final MethodDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
        n.setTypeParameters(modifyList(n.getTypeParameters(), arg));
		n.setElementType((Type) n.getElementType().accept(this, arg));
		n.setParameters((NodeList<Parameter>)n.getParameters().accept(this, arg));
        n.setThrows((NodeList<ReferenceType<?>>)n.getThrows().accept(this, arg));
        n.setBody(n.getBody().flatMap(p -> option((BlockStmt) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final NameExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final NormalAnnotationExpr n, final A arg) {
		visitComment(n, arg);
		n.setName((NameExpr) n.getName().accept(this, arg));
        n.setPairs((NodeList<MemberValuePair>)n.getPairs().accept(this, arg));
		return n;
	}

	@Override public Node visit(final NullLiteralExpr n, final A arg) {
		visitComment(n, arg);
		return n;
	}

	@Override public Node visit(final ObjectCreationExpr n, final A arg) {
		visitComment(n, arg);
        n.setScope(n.getScope().flatMap(p -> option((Expression) p.accept(this, arg))));
        n.setTypeArguments(n.getTypeArguments().flatMap(p -> option((NodeList<Type<?>>) modifyList(p, arg))));
		n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
        n.setArgs((NodeList<Expression>)n.getArgs().accept(this, arg));
        n.setAnonymousClassBody(n.getAnonymousClassBody().flatMap(p -> option((NodeList<BodyDeclaration<?>>) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final PackageDeclaration n, final A arg) {
		visitComment(n, arg);
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}
	
	@Override public Node visit(final Parameter n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		n.setId((VariableDeclaratorId) n.getId().accept(this, arg));
		n.setElementType((Type) n.getElementType().accept(this, arg));
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

	@Override
	public Node visit(ArrayType n, A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
		n.setComponentType((Type) n.getComponentType().accept(this, arg));
		return n;
	}

	@Override
	public Node visit(ArrayCreationLevel n, A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
        n.setDimension(n.getDimension().flatMap(p -> option((Expression) p.accept(this, arg))));
		return n;
	}

	@Override
    public Node visit(final IntersectionType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
        n.setElements((NodeList<ReferenceType<?>>)n.getElements().accept(this, arg));
        return n;
    }

    @Override
    public Node visit(final UnionType n, final A arg) {
		visitComment(n, arg);
		visitAnnotations(n, arg);
        n.setElements((NodeList<ReferenceType<?>>)n.getElements().accept(this, arg));
        return n;
    }

	@Override public Node visit(final ReturnStmt n, final A arg) {
		visitComment(n, arg);
        n.setExpr(n.getExpr().flatMap(p -> option((Expression) p.accept(this, arg))));
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
        n.setClassExpr(n.getClassExpr().flatMap(p -> option((Expression) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final SwitchEntryStmt n, final A arg) {
		visitComment(n, arg);
		if (n.getLabel() != null) {
			n.setLabel((Expression) n.getLabel().accept(this, arg));
		}
		n.setStmts((NodeList<Statement>) n.getStmts().accept(this, arg));
		return n;
	}

	@Override public Node visit(final SwitchStmt n, final A arg) {
		visitComment(n, arg);
		n.setSelector((Expression) n.getSelector().accept(this, arg));
        n.setEntries((NodeList<SwitchEntryStmt>)n.getEntries().accept(this, arg));
		return n;

	}

	@Override public Node visit(final SynchronizedStmt n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		n.setBody((BlockStmt) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ThisExpr n, final A arg) {
		visitComment(n, arg);
        n.setClassExpr(n.getClassExpr().flatMap(p -> option((Expression) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final ThrowStmt n, final A arg) {
		visitComment(n, arg);
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TryStmt n, final A arg) {
		visitComment(n, arg);
        n.setResources((NodeList<VariableDeclarationExpr>)n.getResources().accept(this, arg));
		n.setTryBlock((BlockStmt) n.getTryBlock().accept(this, arg));
        n.setCatchs((NodeList<CatchClause>)n.getCatchs().accept(this, arg));
        n.setFinallyBlock(n.getFinallyBlock().flatMap(p -> option((BlockStmt) p.accept(this, arg))));
		return n;
	}

	@Override public Node visit(final TypeDeclarationStmt n, final A arg) {
		visitComment(n, arg);
		n.setTypeDeclaration((TypeDeclaration<?>) n.getTypeDeclaration().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TypeParameter n, final A arg) {
		visitComment(n, arg);
        n.setTypeBound((NodeList<ClassOrInterfaceType>)n.getTypeBound().accept(this, arg));
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
		n.setAnnotations((NodeList<AnnotationExpr>)n.getAnnotations().accept(this, arg));

		final Type type = (Type) n.getElementType().accept(this, arg);
		if (type == null) {
			return null;
		}
		n.setElementType(type);

        n.setVariables((NodeList<VariableDeclarator>)n.getVariables().accept(this, arg));

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
        n.setInit(n.getInit().flatMap(p -> option((Expression) p.accept(this, arg))));
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
        n.setExtends(n.getExtends().flatMap(p -> option((ReferenceType<?>) p.accept(this, arg))));
        n.setSuper(n.getSuper().flatMap(p -> option((ReferenceType<?>) p.accept(this, arg))));
		return n;
	}

	@Override
	public Node visit(final LambdaExpr n, final A arg) {
		visitComment(n, arg);
        n.setParameters((NodeList<Parameter>)n.getParameters().accept(this, arg));
		if (n.getBody() != null) {
			n.setBody((Statement) n.getBody().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final MethodReferenceExpr n, final A arg) {
		visitComment(n, arg);
        n.setTypeArguments(n.getTypeArguments().flatMap(p -> option((NodeList<Type<?>>) modifyList(p, arg))));
		if (n.getScope() != null) {
			n.setScope((Expression)n.getScope().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(final TypeExpr n, final A arg) {
		visitComment(n, arg);
		if (n.getType() != null) {
            n.setType((Type<?>) n.getType().accept(this, arg));
		}
		return n;
	}

	@Override
	public Node visit(ArrayBracketPair n, A arg) {
		visitAnnotations(n, arg);
		return n;
	}

	@Override
	public Node visit(NodeList n, A arg) {
		for (int i = 0; i < n.size(); i++) {
			n.set(i, n.get(i).accept(this, arg));
		}
		for (int i = n.size() - 1; i >= 0; i--) {
			if (n.get(i) == null) {
				n.remove(i);
			}
		}
		return n;
	}

    @Override
	public Node visit(EmptyImportDeclaration n, A arg) {
        visitComment(n, arg);
        return n;
	}

	@Override
	public Node visit(SingleStaticImportDeclaration n, A arg) {
        visitComment(n, arg);
        n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
        return n;
	}

	@Override
	public Node visit(SingleTypeImportDeclaration n, A arg) {
        visitComment(n, arg);
        n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
        return n;
	}

	@Override
	public Node visit(StaticImportOnDemandDeclaration n, A arg) {
        visitComment(n, arg);
        n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
        return n;
	}

	@Override
	public Node visit(TypeImportOnDemandDeclaration n, A arg) {
        visitComment(n, arg);
        n.setName((NameExpr) n.getName().accept(this, arg));
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
        if(n!=null)
            n.setComment(n.getComment().flatMap(dv -> option((Comment) dv.accept(this, arg))));
	}
}
