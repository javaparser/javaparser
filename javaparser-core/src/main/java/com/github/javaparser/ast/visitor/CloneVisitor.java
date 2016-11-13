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
import com.github.javaparser.ast.nodeTypes.NodeWithArrays;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class CloneVisitor implements GenericVisitor<Node, Object> {

	@Override
	public Node visit(CompilationUnit _n, Object _arg) {
		PackageDeclaration package_ = cloneNodes(_n.getPackage(), _arg);
		List<ImportDeclaration> importsList = visit(_n.getImportsList(), _arg);
        List<TypeDeclaration<?>> typesList = visit(_n.getTypesList(), _arg);

		return new CompilationUnit(
				_n.getRange(),
				package_, importsList, typesList
		);
	}

	@Override
	public Node visit(PackageDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		PackageDeclaration r = new PackageDeclaration(
				_n.getRange(),
				annotationsList, name
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ImportDeclaration _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ImportDeclaration r = new ImportDeclaration(
				_n.getRange(),
				name, _n.isStatic(), _n.isAsterisk()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TypeParameter _n, Object _arg) {
        List<ClassOrInterfaceType> typeBound = visit(_n.getTypeBoundList(), _arg);

        List<AnnotationExpr> annotations = visit(_n.getAnnotationsList(), _arg);
        TypeParameter r = new TypeParameter(_n.getRange(),
                _n.getName(), typeBound, annotations);

        Comment comment = cloneNodes(_n.getComment(), _arg);
        r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LineComment _n, Object _arg) {
		return new LineComment(_n.getRange(), _n.getContent());
	}

	@Override
	public Node visit(BlockComment _n, Object _arg) {
		return new BlockComment(_n.getRange(), _n.getContent());
	}

	@Override
	public Node visit(ClassOrInterfaceDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		List<TypeParameter> typeParametersList = visit(_n.getTypeParameterList(), _arg);
		List<ClassOrInterfaceType> extendsList = visit(_n.getExtendsList(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplementsList(), _arg);
        List<BodyDeclaration<?>> membersList = visit(_n.getMembersList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(
				_n.getRange(),
				_n.getModifiers(), annotationsList, _n.isInterface(), _n.getName(), typeParametersList, extendsList, implementsList, membersList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnumDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplementsList(), _arg);
		List<EnumConstantDeclaration> entriesList = visit(_n.getEntriesList(), _arg);
        List<BodyDeclaration<?>> membersList = visit(_n.getMembersList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnumDeclaration r = new EnumDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, _n.getName(), implementsList, entriesList, membersList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyTypeDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyTypeDeclaration r = new EmptyTypeDeclaration(
				_n.getRange()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnumConstantDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		List<Expression> argsList = visit(_n.getArgsList(), _arg);
        List<BodyDeclaration<?>> classBodyList = visit(_n.getClassBodyList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnumConstantDeclaration r = new EnumConstantDeclaration(
				_n.getRange(),
				 annotationsList, _n.getName(), argsList, classBodyList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AnnotationDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
        List<BodyDeclaration<?>> membersList = visit(_n.getMembersList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AnnotationDeclaration r = new AnnotationDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, _n.getName(), membersList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AnnotationMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		Expression defaultValue = cloneNodes(_n.getDefaultValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, type, _n.getName(), defaultValue
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(FieldDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> variablesList = visit(_n.getVariablesList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		FieldDeclaration r = new FieldDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, type, variablesList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclarator _n, Object _arg) {
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Expression init = cloneNodes(_n.getInit(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclarator r = new VariableDeclarator(
				_n.getRange(),
				id, init
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclaratorId _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclaratorId r = new VariableDeclaratorId(
				_n.getRange(),
				_n.getName(), _n.getArrayCount()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ConstructorDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		List<TypeParameter> typeParametersList = visit(_n.getTypeParameterList(), _arg);
		List<Parameter> parametersList = visit(_n.getParametersList(), _arg);
		List<ReferenceType> throwsList = visit(_n.getThrowsList(), _arg);
		BlockStmt block = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ConstructorDeclaration r = new ConstructorDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, typeParametersList, _n.getName(), parametersList, throwsList, block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MethodDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		List<TypeParameter> typeParametersList = visit(_n.getTypeParametersList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		List<Parameter> parametersList = visit(_n.getParametersList(), _arg);
		List<ReferenceType> throwsList = visit(_n.getThrowsList(), _arg);
		BlockStmt block = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MethodDeclaration r = new MethodDeclaration(
				_n.getRange(),
				 _n.getModifiers(), annotationsList, typeParametersList, type, _n.getName(), parametersList, _n.getArrayCount(), throwsList, block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(Parameter _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		Parameter r = new Parameter(
				_n.getRange(),
				_n.getModifiers(), annotationsList, type, _n.isVarArgs(), id
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyMemberDeclaration r = new EmptyMemberDeclaration(
				_n.getRange()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(InitializerDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		InitializerDeclaration r = new InitializerDeclaration(
				_n.getRange(),
				 _n.isStatic(), block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(JavadocComment _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);
		JavadocComment r = new JavadocComment(
				_n.getRange(),
				_n.getContent()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ClassOrInterfaceType _n, Object _arg) {
		ClassOrInterfaceType scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgsList = visit(_n.getTypeArgsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassOrInterfaceType r = new ClassOrInterfaceType(
				_n.getRange(),
				scope, _n.getName(), _n.getTypeArguments()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(PrimitiveType _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);

		PrimitiveType r = new PrimitiveType(
				_n.getRange(),
				_n.getType()
		);
		r.setComment(comment);
		r.setAnnotationsList(annotationsList);
		return r;
	}

	@Override
	public Node visit(ReferenceType _n, Object _arg) {
		List<AnnotationExpr> annList = visit(_n.getAnnotationsList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		List<List<AnnotationExpr>> arraysAnnotationsList = cloneArraysAnnotations(_n, _arg);

        ReferenceType r = new ReferenceType(_n.getBegin().line,
                _n.getBegin().column, _n.getEnd().line, _n.getEnd().column, type,
                _n.getArrayCount(), annList, arraysAnnotationsList);
        Comment comment = cloneNodes(_n.getComment(), _arg);
        r.setComment(comment);
		return r;
	}

    @Override
    public Node visit(IntersectionType _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
        List<ReferenceType> elementsList = visit(_n.getElementsList(), _arg);

        IntersectionType r = new IntersectionType(_n.getRange(), elementsList);
        Comment comment = cloneNodes(_n.getComment(), _arg);
        r.setComment(comment);
		r.setAnnotationsList(annotationsList);
        return r;
    }

    @Override
    public Node visit(UnionType _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
        List<ReferenceType> elementsList = visit(_n.getElementsList(), _arg);

        UnionType r = new UnionType(_n.getRange(),
                elementsList);
        Comment comment = cloneNodes(_n.getComment(), _arg);
        r.setComment(comment);
		r.setAnnotationsList(annotationsList);
        return r;
    }

	@Override
	public Node visit(VoidType _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VoidType r = new VoidType(_n.getRange());
		r.setAnnotationsList(annotationsList);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(WildcardType _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		ReferenceType ext = cloneNodes(_n.getExtends(), _arg);
		ReferenceType sup = cloneNodes(_n.getSuper(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		WildcardType r = new WildcardType(
				_n.getRange(),
				ext, sup
		);
		r.setComment(comment);
		r.setAnnotationsList(annotationsList);
		return r;
	}

	@Override
	public Node visit(UnknownType _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		UnknownType r = new UnknownType();
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ArrayAccessExpr _n, Object _arg) {
		Expression name = cloneNodes(_n.getName(), _arg);
		Expression index = cloneNodes(_n.getIndex(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ArrayAccessExpr r = new ArrayAccessExpr(
				_n.getRange(),
				name, index
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ArrayCreationExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Expression> dimensionsList = visit(_n.getDimensionsList(), _arg);
		ArrayCreationExpr r = new ArrayCreationExpr(_n.getRange(), type_,
				dimensionsList, _n.getArrayCount());
		if (_n.getInitializer() != null) {// ArrayCreationExpr has two mutually
			// exclusive constructors
			r.setInitializer(cloneNodes(_n.getInitializer(), _arg));
		}
		r.setArraysAnnotationsList(cloneArraysAnnotations(_n, _arg));
		Comment comment = cloneNodes(_n.getComment(), _arg);
        r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ArrayInitializerExpr _n, Object _arg) {
		List<Expression> valuesList = visit(_n.getValuesList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ArrayInitializerExpr r = new ArrayInitializerExpr(
				_n.getRange(),
				valuesList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AssignExpr _n, Object _arg) {
		Expression target = cloneNodes(_n.getTarget(), _arg);
		Expression value = cloneNodes(_n.getValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AssignExpr r = new AssignExpr(
				_n.getRange(),
				target, value, _n.getOperator());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BinaryExpr _n, Object _arg) {
		Expression left = cloneNodes(_n.getLeft(), _arg);
		Expression right = cloneNodes(_n.getRight(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BinaryExpr r = new BinaryExpr(
				_n.getRange(),
				left, right, _n.getOperator()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CastExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CastExpr r = new CastExpr(
				_n.getRange(),
				type_, expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ClassExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassExpr r = new ClassExpr(
				_n.getRange(),
				type_
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ConditionalExpr _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Expression thenExpr = cloneNodes(_n.getThenExpr(), _arg);
		Expression elseExpr = cloneNodes(_n.getElseExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ConditionalExpr r = new ConditionalExpr(
				_n.getRange(),
				condition, thenExpr, elseExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnclosedExpr _n, Object _arg) {
		Expression inner = cloneNodes(_n.getInner(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnclosedExpr r = new EnclosedExpr(
				_n.getRange(),
				inner
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(FieldAccessExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgsList = visit(_n.getTypeArgsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		FieldAccessExpr r = new FieldAccessExpr(
				_n.getRange(),
				scope, typeArgsList, _n.getField()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(InstanceOfExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		InstanceOfExpr r = new InstanceOfExpr(
				_n.getRange(),
				expr, type
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(StringLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);
		StringLiteralExpr r = new StringLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IntegerLiteralExpr r = new IntegerLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LongLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LongLiteralExpr r = new LongLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralMinValueExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IntegerLiteralMinValueExpr r = new IntegerLiteralMinValueExpr(_n.getRange());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LongLiteralMinValueExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LongLiteralMinValueExpr r = new LongLiteralMinValueExpr(_n.getRange());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CharLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CharLiteralExpr r = new CharLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(DoubleLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		DoubleLiteralExpr r = new DoubleLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BooleanLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BooleanLiteralExpr r = new BooleanLiteralExpr(
				_n.getRange(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NullLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NullLiteralExpr r = new NullLiteralExpr(_n.getRange());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MethodCallExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgsList = visit(_n.getTypeArgsList(), _arg);
		List<Expression> argsList = visit(_n.getArgsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MethodCallExpr r = new MethodCallExpr(
				_n.getRange(),
				scope, typeArgsList, _n.getName(), argsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NameExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NameExpr r = new NameExpr(
				_n.getRange(),
				_n.getName()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ObjectCreationExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		ClassOrInterfaceType type = cloneNodes(_n.getType(), _arg);
		List<Type> typeArgsList = visit(_n.getTypeArgsList(), _arg);
		List<Expression> argsList = visit(_n.getArgsList(), _arg);
        List<BodyDeclaration<?>> anonymousBodyList = visit(_n.getAnonymousClassBodyList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ObjectCreationExpr r = new ObjectCreationExpr(
				_n.getRange(),
				scope, type, typeArgsList, argsList, anonymousBodyList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(QualifiedNameExpr _n, Object _arg) {
		NameExpr scope = cloneNodes(_n.getQualifier(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		QualifiedNameExpr r = new QualifiedNameExpr(
				_n.getRange(),
				scope, _n.getName()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ThisExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ThisExpr r = new ThisExpr(
				_n.getRange(),
				classExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SuperExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SuperExpr r = new SuperExpr(
				_n.getRange(),
				classExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(UnaryExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		UnaryExpr r = new UnaryExpr(
				_n.getRange(),
				expr, _n.getOperator()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclarationExpr _n, Object _arg) {
		List<AnnotationExpr> annotationsList = visit(_n.getAnnotationsList(), _arg);
		Type type = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> varsList = visit(_n.getVarsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclarationExpr r = new VariableDeclarationExpr(
				_n.getRange(),
				_n.getModifiers(), annotationsList, type, varsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MarkerAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MarkerAnnotationExpr r = new MarkerAnnotationExpr(
				_n.getRange(),
				name
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SingleMemberAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Expression memberValue = cloneNodes(_n.getMemberValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(
				_n.getRange(),
				name, memberValue
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NormalAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		List<MemberValuePair> pairsList = visit(_n.getPairsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NormalAnnotationExpr r = new NormalAnnotationExpr(
				_n.getRange(),
				name, pairsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MemberValuePair _n, Object _arg) {
		Expression value = cloneNodes(_n.getValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MemberValuePair r = new MemberValuePair(
				_n.getRange(),
				_n.getName(), value
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ExplicitConstructorInvocationStmt _n, Object _arg) {
		List<Type> typeArgs = visit(_n.getTypeArgsList(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		List<Expression> argsList = visit(_n.getArgsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(
				_n.getRange(),
				typeArgs, _n.isThis(), expr, argsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TypeDeclarationStmt _n, Object _arg) {
        TypeDeclaration<?> typeDeclaration = cloneNodes(_n.getTypeDeclaration(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		TypeDeclarationStmt r = new TypeDeclarationStmt(
				_n.getRange(),
				typeDeclaration
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AssertStmt _n, Object _arg) {
		Expression check = cloneNodes(_n.getCheck(), _arg);
		Expression message = cloneNodes(_n.getMsg(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AssertStmt r = new AssertStmt(
				_n.getRange(),
				check, message
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BlockStmt _n, Object _arg) {
		List<Statement> stmtsList = visit(_n.getStmtsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BlockStmt r = new BlockStmt(
				_n.getRange(),
				stmtsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LabeledStmt _n, Object _arg) {
		Statement stmt = cloneNodes(_n.getStmt(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LabeledStmt r = new LabeledStmt(
				_n.getRange(),
				_n.getLabel(), stmt
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyStmt r = new EmptyStmt(_n.getRange());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ExpressionStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ExpressionStmt r = new ExpressionStmt(
				_n.getRange(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SwitchStmt _n, Object _arg) {
		Expression selector = cloneNodes(_n.getSelector(), _arg);
		List<SwitchEntryStmt> entriesList = visit(_n.getEntriesList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SwitchStmt r = new SwitchStmt(
				_n.getRange(),
				selector, entriesList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SwitchEntryStmt _n, Object _arg) {
		Expression label = cloneNodes(_n.getLabel(), _arg);
		List<Statement> stmtsList = visit(_n.getStmtsList(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SwitchEntryStmt r = new SwitchEntryStmt(
				_n.getRange(),
				label, stmtsList
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BreakStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BreakStmt r = new BreakStmt(
				_n.getRange(),
				_n.getId()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ReturnStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ReturnStmt r = new ReturnStmt(
				_n.getRange(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IfStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement thenStmt = cloneNodes(_n.getThenStmt(), _arg);
		Statement elseStmt = cloneNodes(_n.getElseStmt(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IfStmt r = new IfStmt(
				_n.getRange(),
				condition, thenStmt, elseStmt
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(WhileStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		WhileStmt r = new WhileStmt(
				_n.getRange(),
				condition, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ContinueStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ContinueStmt r = new ContinueStmt(
				_n.getRange(),
				_n.getId()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(DoStmt _n, Object _arg) {
		Statement body = cloneNodes(_n.getBody(), _arg);
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		DoStmt r = new DoStmt(
				_n.getRange(),
				body, condition
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ForeachStmt _n, Object _arg) {
		VariableDeclarationExpr var = cloneNodes(_n.getVar(), _arg);
		Expression iterable = cloneNodes(_n.getIterable(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ForeachStmt r = new ForeachStmt(
				_n.getRange(),
				var, iterable, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ForStmt _n, Object _arg) {
		List<Expression> initList = visit(_n.getInitList(), _arg);
		Expression compare = cloneNodes(_n.getCompare(), _arg);
		List<Expression> updateList = visit(_n.getUpdateList(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ForStmt r = new ForStmt(
				_n.getRange(),
				initList, compare, updateList, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ThrowStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ThrowStmt r = new ThrowStmt(
				_n.getRange(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SynchronizedStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SynchronizedStmt r = new SynchronizedStmt(
				_n.getRange(),
				expr, block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TryStmt _n, Object _arg) {
		List<VariableDeclarationExpr> resourcesList = visit(_n.getResourcesList(),_arg);
		BlockStmt tryBlock = cloneNodes(_n.getTryBlock(), _arg);
		List<CatchClause> catchsList = visit(_n.getCatchsList(), _arg);
		BlockStmt finallyBlock = cloneNodes(_n.getFinallyBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		TryStmt r = new TryStmt(
				_n.getRange(),
				resourcesList, tryBlock, catchsList, finallyBlock
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CatchClause _n, Object _arg) {
		Parameter param = cloneNodes(_n.getParam(), _arg);
		BlockStmt catchBlock = cloneNodes(_n.getCatchBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CatchClause r = new CatchClause(
				_n.getRange(),
				param.getModifiers(), param.getAnnotationsList(), param.getType(), param.getId(), catchBlock
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LambdaExpr _n, Object _arg) {

		List<Parameter> lambdaParametersList = visit(_n.getParametersList(), _arg);

		Statement body = cloneNodes(_n.getBody(), _arg);

		return new LambdaExpr(_n.getRange(), lambdaParametersList, body,
				_n.isParametersEnclosed());
	}

	@Override
	public Node visit(MethodReferenceExpr _n, Object arg) {

		Expression scope = cloneNodes(_n.getScope(), arg);

		return new MethodReferenceExpr(_n.getRange(), scope,
				_n.getTypeArguments(), _n.getIdentifier());
	}

	@Override
	public Node visit(TypeExpr n, Object arg) {

		Type t = cloneNodes(n.getType(), arg);

		return new TypeExpr(n.getRange(), t);
	}

    public <T extends Node> List<T> visit(List<T> _nodes, Object _arg) {
        if (_nodes == null)
            return null;
        List<T> r = new ArrayList<>(_nodes.size());
        for (T n : _nodes) {
            T rN = cloneNodes(n, _arg);
            if (rN != null)
                r.add(rN);
        }
        return r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNodes(T _node, Object _arg) {
        if (_node == null)
            return null;
        Node r = _node.accept(this, _arg);
        if (r == null)
            return null;
        return (T) r;
    }


	private List<List<AnnotationExpr>> cloneArraysAnnotations(NodeWithArrays<?> _n, Object _arg) {
		List<List<AnnotationExpr>> arraysAnnotations = _n.getArraysAnnotationsList();
		List<List<AnnotationExpr>> _arraysAnnotations = null;
		if(arraysAnnotations != null){
			_arraysAnnotations = new LinkedList<>();
			for(List<AnnotationExpr> aux: arraysAnnotations){
				_arraysAnnotations.add(visit(aux, _arg));
			}
		}
		return _arraysAnnotations;
	}
}
