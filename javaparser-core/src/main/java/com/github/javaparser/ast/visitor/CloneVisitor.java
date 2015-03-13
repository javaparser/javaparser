/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class CloneVisitor implements GenericVisitor<Node, Object> {

	@Override
	public Node visit(CompilationUnit _n, Object _arg) {
		PackageDeclaration package_ = cloneNodes(_n.getPackage(), _arg);
		List<ImportDeclaration> imports = visit(_n.getImports(), _arg);
		List<TypeDeclaration> types = visit(_n.getTypes(), _arg);

		return new CompilationUnit(
				_n.first(), _n.last(),
				package_, imports, types
		);
	}

	@Override
	public Node visit(PackageDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		NameExpr name = cloneNodes(_n.getName(), _arg);

		PackageDeclaration r = new PackageDeclaration(
				_n.first(), _n.last(),
				annotations, name
		);
		return r;
	}

	@Override
	public Node visit(ImportDeclaration _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);

		ImportDeclaration r = new ImportDeclaration(
				_n.first(), _n.last(),
				name, _n.isStatic(), _n.isAsterisk()
		);
		return r;
	}

	@Override
	public Node visit(TypeParameter _n, Object _arg) {
        List<ClassOrInterfaceType> typeBound = visit(_n.getTypeBound(), _arg);

        List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
        TypeParameter r = new TypeParameter(_n.first(), _n.last(),
                _n.getName(), typeBound, annotations);

		return r;
	}

	@Override
	public Node visit(ClassOrInterfaceDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<ClassOrInterfaceType> extendsList = visit(_n.getExtends(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(
				_n.first(), _n.last(),
				_n.getModifiers(), annotations, _n.isInterface(), _n.getName(), typeParameters, extendsList, implementsList, members
		);
		return r;
	}

	@Override
	public Node visit(EnumDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<EnumConstantDeclaration> entries = visit(_n.getEntries(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		EnumDeclaration r = new EnumDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, _n.getName(), implementsList, entries, members
		);
		return r;
	}

	@Override
	public Node visit(EmptyTypeDeclaration _n, Object _arg) {

		EmptyTypeDeclaration r = new EmptyTypeDeclaration(
				_n.first(), _n.last()
		);
		return r;
	}

	@Override
	public Node visit(EnumConstantDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> classBody = visit(_n.getClassBody(), _arg);

		EnumConstantDeclaration r = new EnumConstantDeclaration(
				_n.first(), _n.last(),
				 annotations, _n.getName(), args, classBody
		);
		return r;
	}

	@Override
	public Node visit(AnnotationDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		AnnotationDeclaration r = new AnnotationDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, _n.getName(), members
		);
		return r;
	}

	@Override
	public Node visit(AnnotationMemberDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression defaultValue = cloneNodes(_n.getDefaultValue(), _arg);

		AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, type_, _n.getName(), defaultValue
		);
		return r;
	}

	@Override
	public Node visit(FieldDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> variables = visit(_n.getVariables(), _arg);

		FieldDeclaration r = new FieldDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, type_, variables
		);
		return r;
	}

	@Override
	public Node visit(VariableDeclarator _n, Object _arg) {
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Expression init = cloneNodes(_n.getInit(), _arg);

		VariableDeclarator r = new VariableDeclarator(
				_n.first(), _n.last(),
				id, init
		);
		return r;
	}

	@Override
	public Node visit(VariableDeclaratorId _n, Object _arg) {

		VariableDeclaratorId r = new VariableDeclaratorId(
				_n.first(), _n.last(),
				_n.getName(), _n.getArrayCount()
		);
		return r;
	}

	@Override
	public Node visit(ConstructorDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<Parameter> parameters = visit(_n.getParameters(), _arg);
		List<NameExpr> throws_ = visit(_n.getThrows(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		ConstructorDeclaration r = new ConstructorDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, typeParameters, _n.getName(), parameters, throws_, block
		);
		return r;
	}

	@Override
	public Node visit(MethodDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Parameter> parameters = visit(_n.getParameters(), _arg);
		List<NameExpr> throws_ = visit(_n.getThrows(), _arg);
		BlockStmt block = cloneNodes(_n.getBody(), _arg);

		MethodDeclaration r = new MethodDeclaration(
				_n.first(), _n.last(),
				 _n.getModifiers(), annotations, typeParameters, type_, _n.getName(), parameters, _n.getArrayCount(), throws_, block
		);
		return r;
	}

	@Override
	public Node visit(Parameter _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);

		Parameter r = new Parameter(
				_n.first(), _n.last(),
				_n.getModifiers(), annotations, type_, _n.isVarArgs(), id
		);
		return r;
	}

	@Override
	public Node visit(MultiTypeParameter _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<Type> types = visit(_n.getTypes(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);

		MultiTypeParameter r = new MultiTypeParameter(
				_n.first(), _n.last(),
				_n.getModifiers(), annotations, types, id
		);
		return r;
	}

	@Override
	public Node visit(EmptyMemberDeclaration _n, Object _arg) {

		EmptyMemberDeclaration r = new EmptyMemberDeclaration(
				_n.first(), _n.last()
		);
		return r;
	}

	@Override
	public Node visit(InitializerDeclaration _n, Object _arg) {
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		InitializerDeclaration r = new InitializerDeclaration(
				_n.first(), _n.last(),
				 _n.isStatic(), block
		);
		return r;
	}

	@Override
	public Node visit(ClassOrInterfaceType _n, Object _arg) {
		ClassOrInterfaceType scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);

		ClassOrInterfaceType r = new ClassOrInterfaceType(
				_n.first(), _n.last(),
				scope, _n.getName(), typeArgs
		);
		return r;
	}

	@Override
	public Node visit(PrimitiveType _n, Object _arg) {

		PrimitiveType r = new PrimitiveType(
				_n.first(), _n.last(),
				_n.getType()
		);
		return r;
	}

	@Override
	public Node visit(ReferenceType _n, Object _arg) {
		List<AnnotationExpr> ann = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<List<AnnotationExpr>> arraysAnnotations = _n.getArraysAnnotations();
		List<List<AnnotationExpr>> _arraysAnnotations = null;
		if(arraysAnnotations != null){
			_arraysAnnotations = new LinkedList<List<AnnotationExpr>>();
			for(List<AnnotationExpr> aux: arraysAnnotations){
				_arraysAnnotations.add(visit(aux, _arg));
			}
		}

        ReferenceType r = new ReferenceType(_n.first(), _n.last(), type_,
                _n.getArrayCount(), ann, _arraysAnnotations);
		return r;
	}

	@Override
	public Node visit(VoidType _n, Object _arg) {

		VoidType r = new VoidType(_n.first(), _n.last());
		return r;
	}

	@Override
	public Node visit(WildcardType _n, Object _arg) {
		ReferenceType ext = cloneNodes(_n.getExtends(), _arg);
		ReferenceType sup = cloneNodes(_n.getSuper(), _arg);

		WildcardType r = new WildcardType(
				_n.first(), _n.last(),
				ext, sup
		);
		return r;
	}

	@Override
	public Node visit(ArrayAccessExpr _n, Object _arg) {
		Expression name = cloneNodes(_n.getName(), _arg);
		Expression index = cloneNodes(_n.getIndex(), _arg);

		ArrayAccessExpr r = new ArrayAccessExpr(
				_n.first(), _n.last(),
				name, index
		);
		return r;
	}

	@Override
	public Node visit(ArrayCreationExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Expression> dimensions = visit(_n.getDimensions(), _arg);
		ArrayCreationExpr r = new ArrayCreationExpr(_n.first(), _n.last(), type_,
				dimensions, _n.getArrayCount());
		if (_n.getInitializer() != null) {// ArrayCreationExpr has two mutually
			// exclusive constructors
			r.setInitializer(cloneNodes(_n.getInitializer(), _arg));
		}
		List<List<AnnotationExpr>> arraysAnnotations = _n.getArraysAnnotations();
		List<List<AnnotationExpr>> _arraysAnnotations = null;
		if(arraysAnnotations != null){
			_arraysAnnotations = new LinkedList<List<AnnotationExpr>>();
			for(List<AnnotationExpr> aux: arraysAnnotations){
				_arraysAnnotations.add(visit(aux, _arg));
			}
		}
		r.setArraysAnnotations(_arraysAnnotations);
		return r;
	}

	@Override
	public Node visit(ArrayInitializerExpr _n, Object _arg) {
		List<Expression> values = visit(_n.getValues(), _arg);

		ArrayInitializerExpr r = new ArrayInitializerExpr(
				_n.first(), _n.last(),
				values
		);
        return r;
    }

	@Override
	public Node visit(AssignExpr _n, Object _arg) {
		Expression target = cloneNodes(_n.getTarget(), _arg);
		Expression value = cloneNodes(_n.getValue(), _arg);

		AssignExpr r = new AssignExpr(
				_n.first(), _n.last(),
				target, value, _n.getOperator());
		return r;
	}

	@Override
	public Node visit(BinaryExpr _n, Object _arg) {
		Expression left = cloneNodes(_n.getLeft(), _arg);
		Expression right = cloneNodes(_n.getRight(), _arg);

		BinaryExpr r = new BinaryExpr(
				_n.first(), _n.last(),
				left, right, _n.getOperator()
		);
		return r;
	}

	@Override
	public Node visit(CastExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		CastExpr r = new CastExpr(
				_n.first(), _n.last(),
				type_, expr
		);
		return r;
	}

	@Override
	public Node visit(ClassExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);

		ClassExpr r = new ClassExpr(
				_n.first(), _n.last(),
				type_
		);
        return r;
    }

	@Override
	public Node visit(ConditionalExpr _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Expression thenExpr = cloneNodes(_n.getThenExpr(), _arg);
		Expression elseExpr = cloneNodes(_n.getElseExpr(), _arg);

		ConditionalExpr r = new ConditionalExpr(
				_n.first(), _n.last(),
				condition, thenExpr, elseExpr
		);
		return r;
	}

	@Override
	public Node visit(EnclosedExpr _n, Object _arg) {
		Expression inner = cloneNodes(_n.getInner(), _arg);

		EnclosedExpr r = new EnclosedExpr(
				_n.first(), _n.last(),
				inner
		);
        return r;
    }

	@Override
	public Node visit(FieldAccessExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);

		FieldAccessExpr r = new FieldAccessExpr(
				_n.first(), _n.last(),
				scope, typeArgs, _n.getField()
		);
		return r;
	}

	@Override
	public Node visit(InstanceOfExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);

		InstanceOfExpr r = new InstanceOfExpr(
				_n.first(), _n.last(),
				expr, type_
		);
		return r;
	}

	@Override
	public Node visit(StringLiteralExpr _n, Object _arg) {
		StringLiteralExpr r = new StringLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralExpr _n, Object _arg) {

		IntegerLiteralExpr r = new IntegerLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(LongLiteralExpr _n, Object _arg) {

		LongLiteralExpr r = new LongLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralMinValueExpr _n, Object _arg) {

		IntegerLiteralMinValueExpr r = new IntegerLiteralMinValueExpr(_n.first(), _n.last());
		return r;
	}

    @Override
    public Node visit(LongLiteralMinValueExpr _n, Object _arg) {

		LongLiteralMinValueExpr r = new LongLiteralMinValueExpr(_n.first(), _n.last());
		return r;
	}

    @Override
    public Node visit(CharLiteralExpr _n, Object _arg) {

		CharLiteralExpr r = new CharLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(DoubleLiteralExpr _n, Object _arg) {

		DoubleLiteralExpr r = new DoubleLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(BooleanLiteralExpr _n, Object _arg) {

		BooleanLiteralExpr r = new BooleanLiteralExpr(
				_n.first(), _n.last(),
				_n.getValue()
		);
		return r;
	}

	@Override
	public Node visit(NullLiteralExpr _n, Object _arg) {

		NullLiteralExpr r = new NullLiteralExpr(_n.first(), _n.last());
		return r;
	}

    @Override
    public Node visit(MethodCallExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);

		MethodCallExpr r = new MethodCallExpr(
				_n.first(), _n.last(),
				scope, typeArgs, _n.getName(), args
        );
		return r;
	}

	@Override
	public Node visit(NameExpr _n, Object _arg) {

		NameExpr r = new NameExpr(
				_n.first(), _n.last(),
				_n.getName()
		);
		return r;
	}

	@Override
	public Node visit(ObjectCreationExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		ClassOrInterfaceType type_ = cloneNodes(_n.getType(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> anonymousBody = visit(_n.getAnonymousClassBody(), _arg);

		ObjectCreationExpr r = new ObjectCreationExpr(
				_n.first(), _n.last(),
				scope, type_, typeArgs, args, anonymousBody
		);
		return r;
	}

	@Override
	public Node visit(QualifiedNameExpr _n, Object _arg) {
		NameExpr scope = cloneNodes(_n.getQualifier(), _arg);

		QualifiedNameExpr r = new QualifiedNameExpr(
				_n.first(), _n.last(),
				scope, _n.getName()
		);
        return r;
	}

	@Override
	public Node visit(ThisExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);

		ThisExpr r = new ThisExpr(
				_n.first(), _n.last(),
				classExpr
		);
		return r;
	}

	@Override
	public Node visit(SuperExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);

		SuperExpr r = new SuperExpr(
				_n.first(), _n.last(),
				classExpr
		);
		return r;
	}

	@Override
	public Node visit(UnaryExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		UnaryExpr r = new UnaryExpr(
				_n.first(), _n.last(),
				expr, _n.getOperator()
		);
		return r;
	}

	@Override
	public Node visit(VariableDeclarationExpr _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> vars = visit(_n.getVars(), _arg);

		VariableDeclarationExpr r = new VariableDeclarationExpr(
				_n.first(), _n.last(),
				_n.getModifiers(), annotations, type_, vars
		);
		return r;
	}

	@Override
	public Node visit(MarkerAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);

		MarkerAnnotationExpr r = new MarkerAnnotationExpr(
				_n.first(), _n.last(),
				name
		);
        return r;
    }

    @Override
	public Node visit(SingleMemberAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Expression memberValue = cloneNodes(_n.getMemberValue(), _arg);

		SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(
				_n.first(), _n.last(),
				name, memberValue
		);
        return r;
	}

	@Override
	public Node visit(NormalAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		List<MemberValuePair> pairs = visit(_n.getPairs(), _arg);

		NormalAnnotationExpr r = new NormalAnnotationExpr(
				_n.first(), _n.last(),
				name, pairs
		);
		return r;
	}

	@Override
	public Node visit(MemberValuePair _n, Object _arg) {
		Expression value = cloneNodes(_n.getValue(), _arg);

		MemberValuePair r = new MemberValuePair(
				_n.first(), _n.last(),
				_n.getName(), value
		);
        return r;
	}

	@Override
	public Node visit(ExplicitConstructorInvocationStmt _n, Object _arg) {
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);

		ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(
				_n.first(), _n.last(),
				typeArgs, _n.isThis(), expr, args
		);
		return r;
	}

	@Override
	public Node visit(TypeDeclarationStmt _n, Object _arg) {
		TypeDeclaration typeDecl = cloneNodes(_n.getTypeDeclaration(), _arg);

		TypeDeclarationStmt r = new TypeDeclarationStmt(
				_n.first(), _n.last(),
				typeDecl
		);
        return r;
	}

	@Override
	public Node visit(AssertStmt _n, Object _arg) {
		Expression check = cloneNodes(_n.getCheck(), _arg);
		Expression message = cloneNodes(_n.getMessage(), _arg);

		AssertStmt r = new AssertStmt(
				_n.first(), _n.last(),
				check, message
		);
		return r;
	}

	@Override
	public Node visit(BlockStmt _n, Object _arg) {
		List<Statement> stmts = visit(_n.getStmts(), _arg);

		BlockStmt r = new BlockStmt(
				_n.first(), _n.last(),
				stmts
		);
        return r;
    }

	@Override
	public Node visit(LabeledStmt _n, Object _arg) {
		Statement stmt = cloneNodes(_n.getStmt(), _arg);

		LabeledStmt r = new LabeledStmt(
				_n.first(), _n.last(),
				_n.getLabel(), stmt
		);
        return r;
	}

	@Override
	public Node visit(EmptyStmt _n, Object _arg) {

		EmptyStmt r = new EmptyStmt(_n.first(), _n.last());
		return r;
	}

    @Override
    public Node visit(ExpressionStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpression(), _arg);

		ExpressionStmt r = new ExpressionStmt(
				_n.first(), _n.last(),
				expr
		);
        return r;
    }

    @Override
	public Node visit(SwitchStmt _n, Object _arg) {
		Expression selector = cloneNodes(_n.getSelector(), _arg);
		List<SwitchEntryStmt> entries = visit(_n.getEntries(), _arg);

		SwitchStmt r = new SwitchStmt(
				_n.first(), _n.last(),
				selector, entries
		);
        return r;
	}

	@Override
	public Node visit(SwitchEntryStmt _n, Object _arg) {
		Expression label = cloneNodes(_n.getLabel(), _arg);
		List<Statement> stmts = visit(_n.getStmts(), _arg);

		SwitchEntryStmt r = new SwitchEntryStmt(
				_n.first(), _n.last(),
				label, stmts
		);
		return r;
	}

	@Override
	public Node visit(BreakStmt _n, Object _arg) {

		BreakStmt r = new BreakStmt(
				_n.first(), _n.last(),
				_n.getId()
		);
		return r;
	}

	@Override
	public Node visit(ReturnStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		ReturnStmt r = new ReturnStmt(
				_n.first(), _n.last(),
				expr
		);
        return r;
    }

    @Override
	public Node visit(IfStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement thenStmt = cloneNodes(_n.getThenStmt(), _arg);
		Statement elseStmt = cloneNodes(_n.getElseStmt(), _arg);

		IfStmt r = new IfStmt(
				_n.first(), _n.last(),
				condition, thenStmt, elseStmt
		);
		return r;
	}

	@Override
	public Node visit(WhileStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		WhileStmt r = new WhileStmt(
				_n.first(), _n.last(),
				condition, body
		);
        return r;
	}

	@Override
	public Node visit(ContinueStmt _n, Object _arg) {

		ContinueStmt r = new ContinueStmt(
				_n.first(), _n.last(),
				_n.getId()
		);
		return r;
	}

	@Override
	public Node visit(DoStmt _n, Object _arg) {
		Statement body = cloneNodes(_n.getBody(), _arg);
		Expression condition = cloneNodes(_n.getCondition(), _arg);

		DoStmt r = new DoStmt(
				_n.first(), _n.last(),
				body, condition
		);
        return r;
	}

	@Override
	public Node visit(ForeachStmt _n, Object _arg) {
		VariableDeclarationExpr var = cloneNodes(_n.getVariable(), _arg);
		Expression iterable = cloneNodes(_n.getIterable(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		ForeachStmt r = new ForeachStmt(
				_n.first(), _n.last(),
				var, iterable, body
		);
        return r;
	}

	@Override
	public Node visit(ForStmt _n, Object _arg) {
		List<Expression> init = visit(_n.getInit(), _arg);
		Expression compare = cloneNodes(_n.getCompare(), _arg);
		List<Expression> update = visit(_n.getUpdate(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		ForStmt r = new ForStmt(
				_n.first(), _n.last(),
				init, compare, update, body
		);
		return r;
	}

	@Override
	public Node visit(ThrowStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		ThrowStmt r = new ThrowStmt(
				_n.first(), _n.last(),
				expr
		);
        return r;
    }

    @Override
	public Node visit(SynchronizedStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		SynchronizedStmt r = new SynchronizedStmt(
				_n.first(), _n.last(),
				expr, block
		);
		return r;
	}

	@Override
	public Node visit(TryStmt _n, Object _arg) {
		List<VariableDeclarationExpr> resources = visit(_n.getResources(),_arg);
		BlockStmt tryBlock = cloneNodes(_n.getTryBlock(), _arg);
		List<CatchClause> catchs = visit(_n.getCatchs(), _arg);
		BlockStmt finallyBlock = cloneNodes(_n.getFinallyBlock(), _arg);

		TryStmt r = new TryStmt(
				_n.first(), _n.last(),
				resources, tryBlock, catchs, finallyBlock
		);
		return r;
	}

	@Override
	public Node visit(CatchClause _n, Object _arg) {
		MultiTypeParameter except = cloneNodes(_n.getExcept(), _arg);
		BlockStmt catchBlock = cloneNodes(_n.getCatchBlock(), _arg);

		CatchClause r = new CatchClause(
				_n.first(), _n.last(),
				new MultiTypeParameter(except.first(), except.last(),
                        except.getModifiers(), except.getAnnotations(),
                        except.getTypes(), except.getId()),
                catchBlock
		);
		return r;
	}

	@Override
	public Node visit(LambdaExpr _n, Object _arg) {

		List<Parameter> lambdaParameters = visit(_n.getParameters(), _arg);

		Statement body = cloneNodes(_n.getBody(), _arg);

		LambdaExpr r = new LambdaExpr(_n.first(), _n.last(), lambdaParameters, body,
				_n.isParametersEnclosed());

		return r;
	}

	@Override
	public Node visit(MethodReferenceExpr _n, Object arg) {

		List<TypeParameter> typeParams = visit(_n.getTypeParameters(), arg);
		Expression scope = cloneNodes(_n.getScope(), arg);

		MethodReferenceExpr r = new MethodReferenceExpr(_n.first(), _n.last(), scope,
				typeParams, _n.getIdentifier());
		return r;
	}

	@Override
	public Node visit(TypeExpr _n, Object arg) {

		Type t = cloneNodes(_n.getType(), arg);

		TypeExpr r = new TypeExpr(_n.first(), _n.last(), t);

		return r;
	}

    public <T extends Node> List<T> visit(List<T> _nodes, Object _arg) {
        if (_nodes == null)
            return null;
        List<T> r = new ArrayList<T>(_nodes.size());
        for (T n : _nodes) {
            T rN = cloneNodes(n, _arg);
            if (rN != null)
                r.add(rN);
        }
        return r;
    }

    protected <T extends Node> T cloneNodes(T _node, Object _arg) {
        if (_node == null)
            return null;
        Node r = _node.accept(this, _arg);
        if (r == null)
            return null;
        r.setCommentAttributes(cloneComments(_node.getCommentAttributes()));
        return (T) r;
    }

    private CommentAttributes cloneComments(CommentAttributes comments) {
        if (comments == null)
            return null;
        CommentAttributes r = new CommentAttributes();
        r.setLeadingComments(cloneComments(comments.getLeadingComments()));
        r.setDanglingComments(cloneComments(comments.getDanglingComments()));
        r.setTrailingComment(cloneComment(comments.getTrailingComment()));
        return r;
    }

    public List<Comment> cloneComments(List<Comment> comments) {
        if (comments == null)
            return null;
        List<Comment> r = new ArrayList<Comment>(comments.size());
        for (Comment comment : comments) {
            Comment rComment = cloneComment(comment);
            if (rComment != null)
                r.add(rComment);
        }
        return r;
    }

    private Comment cloneComment(Comment comment) {
        if (comment == null)
            return null;
        return new Comment(comment.getCommentKind(), comment.image());
    }
}
