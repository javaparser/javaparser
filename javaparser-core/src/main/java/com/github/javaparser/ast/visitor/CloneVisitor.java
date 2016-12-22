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
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.Optional;

public class CloneVisitor implements GenericVisitor<Visitable, Object> {

    @Override
    public Visitable visit(CompilationUnit _n, Object _arg) {
        PackageDeclaration package_ = cloneNode(_n.getPackageDeclaration(), _arg);
        NodeList<ImportDeclaration> imports = cloneList(_n.getImports(), _arg);
        NodeList<TypeDeclaration<?>> types = cloneList(_n.getTypes(), _arg);

        return new CompilationUnit(
                _n.getRange().orElse(null),
                package_, imports, types
        );
    }

    @Override
    public Visitable visit(PackageDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        PackageDeclaration r = new PackageDeclaration(
                _n.getRange().orElse(null),
                annotations,
                cloneNode(_n.getName(), _arg)
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TypeParameter _n, Object _arg) {
        NodeList<ClassOrInterfaceType> typeBound = cloneList(_n.getTypeBound(), _arg);
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        TypeParameter r = new TypeParameter(_n.getRange().orElse(null),
                _n.getName(), typeBound, annotations);

        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LineComment _n, Object _arg) {
        return new LineComment(_n.getRange().orElse(null), _n.getContent());
    }

    @Override
    public Visitable visit(BlockComment _n, Object _arg) {
        return new BlockComment(_n.getRange().orElse(null), _n.getContent());
    }

    @Override
    public Visitable visit(ClassOrInterfaceDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<TypeParameter> typeParameters = cloneList(_n.getTypeParameters(), _arg);
        NodeList<ClassOrInterfaceType> extendsList = cloneList(_n.getExtendedTypes(), _arg);
        NodeList<ClassOrInterfaceType> implementsList = cloneList(_n.getImplementedTypes(), _arg);
        NodeList<BodyDeclaration<?>> members = cloneList(_n.getMembers(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);
        SimpleName nameExpr_ = cloneNode(_n.getName(), _arg);

        ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(), annotations, _n.isInterface(), nameExpr_, typeParameters, extendsList, implementsList, members
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnumDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<ClassOrInterfaceType> implementsList = cloneList(_n.getImplementedTypes(), _arg);
        NodeList<EnumConstantDeclaration> entries = cloneList(_n.getEntries(), _arg);
        NodeList<BodyDeclaration<?>> members = cloneList(_n.getMembers(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);
        SimpleName nameExpr_ = cloneNode(_n.getName(), _arg);

        EnumDeclaration r = new EnumDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(), annotations, nameExpr_, implementsList, entries, members
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnumConstantDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<Expression> args = cloneList(_n.getArguments(), _arg);
        NodeList<BodyDeclaration<?>> classBody = cloneList(_n.getClassBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        EnumConstantDeclaration r = new EnumConstantDeclaration(
                _n.getRange().orElse(null),
                annotations,
                cloneNode(_n.getName(), _arg),
                args,
                classBody
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AnnotationDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<BodyDeclaration<?>> members = cloneList(_n.getMembers(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);
        SimpleName nameExpr_ = cloneNode(_n.getName(), _arg);

        AnnotationDeclaration r = new AnnotationDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(), annotations, nameExpr_, members
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AnnotationMemberDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Type type_ = cloneNode(_n.getType(), _arg);
        Expression defaultValue = cloneNode(_n.getDefaultValue(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(), annotations, type_, _n.getName(), defaultValue
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(FieldDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations_ = cloneList(_n.getAnnotations(), _arg);
        NodeList<VariableDeclarator> variables_ = cloneList(_n.getVariables(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        FieldDeclaration r = new FieldDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(),
                annotations_,
                variables_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(VariableDeclarator _n, Object _arg) {
        SimpleName id = cloneNode(_n.getName(), _arg);
        Expression init = cloneNode(_n.getInitializer(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);
        Type type = cloneNode(_n.getType(), _arg);

        VariableDeclarator r = new VariableDeclarator(
                _n.getRange().orElse(null),
                type,
                id, 
                init
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ConstructorDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<TypeParameter> typeParameters = cloneList(_n.getTypeParameters(), _arg);
        NodeList<Parameter> parameters = cloneList(_n.getParameters(), _arg);
        NodeList<ReferenceType> throws_ = cloneList(_n.getThrownExceptions(), _arg);
        BlockStmt block = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);
        SimpleName nameExpr_ = cloneNode(_n.getName(), _arg);

        ConstructorDeclaration r = new ConstructorDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(), annotations, typeParameters, nameExpr_, parameters, throws_, block
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MethodDeclaration _n, Object _arg) {
        NodeList<AnnotationExpr> annotations_ = cloneList(_n.getAnnotations(), _arg);
        NodeList<TypeParameter> typeParameters_ = cloneList(_n.getTypeParameters(), _arg);
        Type type_ = cloneNode(_n.getType(), _arg);
        SimpleName nameExpr_ = cloneNode(_n.getName(), _arg);
        NodeList<Parameter> parameters_ = cloneList(_n.getParameters(), _arg);
        NodeList<ReferenceType> throws_ = cloneList(_n.getThrownExceptions(), _arg);
        BlockStmt block_ = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        MethodDeclaration r = new MethodDeclaration(
                _n.getRange().orElse(null),
                _n.getModifiers(),
                annotations_,
                typeParameters_,
                type_,
                nameExpr_,
                _n.isDefault(),
                parameters_,
                throws_,
                block_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(Parameter _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Type type_ = cloneNode(_n.getType(), _arg);
        SimpleName id = cloneNode(_n.getName(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        Parameter r = new Parameter(
                _n.getRange().orElse(null),
                _n.getModifiers(),
                annotations,
                type_,
                _n.isVarArgs(),
                id
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EmptyMemberDeclaration _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        EmptyMemberDeclaration r = new EmptyMemberDeclaration(
                _n.getRange().orElse(null)
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(InitializerDeclaration _n, Object _arg) {
        BlockStmt block = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        InitializerDeclaration r = new InitializerDeclaration(
                _n.getRange().orElse(null),
                _n.isStatic(), block
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(JavadocComment _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);
        JavadocComment r = new JavadocComment(
                _n.getRange().orElse(null),
                _n.getContent()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ClassOrInterfaceType _n, Object _arg) {
        ClassOrInterfaceType scope = cloneNode(_n.getScope(), _arg);
        NodeList<Type> typeArguments = cloneList(_n.getTypeArguments().orElse(null), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ClassOrInterfaceType r = new ClassOrInterfaceType(
                _n.getRange().orElse(null),
                scope,
                _n.getName(),
                typeArguments
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(PrimitiveType _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);

        PrimitiveType r = new PrimitiveType(
                _n.getRange().orElse(null),
                _n.getType()
        );
        r.setComment(comment);
        r.setAnnotations(annotations);
        return r;
    }

    @Override
    public Visitable visit(ArrayType _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Type type_ = cloneNode(_n.getComponentType(), _arg);

        ArrayType r = new ArrayType(_n.getRange().orElse(null), type_, annotations);
        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayCreationLevel _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Expression dimension_ = cloneNode(_n.getDimension(), _arg);

        ArrayCreationLevel r = new ArrayCreationLevel(_n.getRange().orElse(null), dimension_, annotations);

        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IntersectionType _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<ReferenceType> elements = cloneList(_n.getElements(), _arg);

        IntersectionType r = new IntersectionType(_n.getRange().orElse(null), elements);
        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        r.setAnnotations(annotations);
        return r;
    }

    @Override
    public Visitable visit(UnionType _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<ReferenceType> elements = cloneList(_n.getElements(), _arg);

        UnionType r = new UnionType(_n.getRange().orElse(null), elements);
        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        r.setAnnotations(annotations);
        return r;
    }

    @Override
    public Visitable visit(VoidType _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        VoidType r = new VoidType(_n.getRange().orElse(null));
        r.setAnnotations(annotations);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(WildcardType _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        ReferenceType ext = cloneNode(_n.getExtendedTypes(), _arg);
        ReferenceType sup = cloneNode(_n.getSuperTypes(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        WildcardType r = new WildcardType(
                _n.getRange().orElse(null),
                ext, sup
        );
        r.setComment(comment);
        r.setAnnotations(annotations);
        return r;
    }

    @Override
    public Visitable visit(UnknownType _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        UnknownType r = new UnknownType();
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayAccessExpr _n, Object _arg) {
        Expression name = cloneNode(_n.getName(), _arg);
        Expression index = cloneNode(_n.getIndex(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ArrayAccessExpr r = new ArrayAccessExpr(
                _n.getRange().orElse(null),
                name, index
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayCreationExpr _n, Object _arg) {
        Type type_ = cloneNode(_n.getElementType(), _arg);
        NodeList<ArrayCreationLevel> levels_ = cloneList(_n.getLevels(), _arg);
        ArrayInitializerExpr initializer_ = cloneNode(_n.getInitializer(), _arg);

        ArrayCreationExpr r = new ArrayCreationExpr(_n.getRange().orElse(null), type_, levels_, initializer_);

        Comment comment = cloneNode(_n.getComment(), _arg);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayInitializerExpr _n, Object _arg) {
        NodeList<Expression> values = cloneList(_n.getValues(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ArrayInitializerExpr r = new ArrayInitializerExpr(
                _n.getRange().orElse(null),
                values
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AssignExpr _n, Object _arg) {
        Expression target = cloneNode(_n.getTarget(), _arg);
        Expression value = cloneNode(_n.getValue(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        AssignExpr r = new AssignExpr(
                _n.getRange().orElse(null),
                target, value, _n.getOperator());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BinaryExpr _n, Object _arg) {
        Expression left = cloneNode(_n.getLeft(), _arg);
        Expression right = cloneNode(_n.getRight(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        BinaryExpr r = new BinaryExpr(
                _n.getRange().orElse(null),
                left, right, _n.getOperator()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CastExpr _n, Object _arg) {
        Type type_ = cloneNode(_n.getType(), _arg);
        Expression expr = cloneNode(_n.getExpression(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        CastExpr r = new CastExpr(
                _n.getRange().orElse(null),
                type_, expr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ClassExpr _n, Object _arg) {
        Type type_ = cloneNode(_n.getType(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ClassExpr r = new ClassExpr(
                _n.getRange().orElse(null),
                type_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ConditionalExpr _n, Object _arg) {
        Expression condition = cloneNode(_n.getCondition(), _arg);
        Expression thenExpr = cloneNode(_n.getThenExpr(), _arg);
        Expression elseExpr = cloneNode(_n.getElseExpr(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ConditionalExpr r = new ConditionalExpr(
                _n.getRange().orElse(null),
                condition, thenExpr, elseExpr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnclosedExpr _n, Object _arg) {
        Expression inner = cloneNode(_n.getInner(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        EnclosedExpr r = new EnclosedExpr(
                _n.getRange().orElse(null),
                inner
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(FieldAccessExpr _n, Object _arg) {
        Expression scope_ = cloneNode(_n.getScope(), _arg);
        NodeList<Type> typeArguments_ = cloneList(_n.getTypeArguments().orElse(null), _arg);
        SimpleName fieldExpr_ = cloneNode(_n.getField(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        FieldAccessExpr r = new FieldAccessExpr(
                _n.getRange().orElse(null),
                scope_,
                typeArguments_,
                fieldExpr_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(InstanceOfExpr _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        ReferenceType type_ = cloneNode(_n.getType(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        InstanceOfExpr r = new InstanceOfExpr(
                _n.getRange().orElse(null),
                expr, type_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(StringLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);
        StringLiteralExpr r = new StringLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IntegerLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        IntegerLiteralExpr r = new IntegerLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LongLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        LongLiteralExpr r = new LongLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CharLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        CharLiteralExpr r = new CharLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(DoubleLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        DoubleLiteralExpr r = new DoubleLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BooleanLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        BooleanLiteralExpr r = new BooleanLiteralExpr(
                _n.getRange().orElse(null),
                _n.getValue()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NullLiteralExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        NullLiteralExpr r = new NullLiteralExpr(_n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MethodCallExpr _n, Object _arg) {
        Expression scope_ = cloneNode(_n.getScope(), _arg);
        NodeList<Type> typeArguments_ = cloneList(_n.getTypeArguments().orElse(null), _arg);
        NodeList<Expression> args = cloneList(_n.getArguments(), _arg);
        SimpleName nameExpr = cloneNode(_n.getName(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        MethodCallExpr r = new MethodCallExpr(
                _n.getRange().orElse(null),
                scope_,
                typeArguments_,
                nameExpr,
                args
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NameExpr _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        NameExpr r = new NameExpr(
                _n.getRange().orElse(null),
                _n.getName()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ObjectCreationExpr _n, Object _arg) {
        Expression scope = cloneNode(_n.getScope(), _arg);
        ClassOrInterfaceType type_ = cloneNode(_n.getType(), _arg);
        NodeList<Type> typeArguments = cloneList(_n.getTypeArguments().orElse(null), _arg);
        NodeList<Expression> args = cloneList(_n.getArguments(), _arg);
        NodeList<BodyDeclaration<?>> anonymousBody = cloneList(_n.getAnonymousClassBody().orElse(null), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ObjectCreationExpr r = new ObjectCreationExpr(
                _n.getRange().orElse(null),
                scope, type_, typeArguments, args, anonymousBody
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(Name _n, Object _arg) {
        Name scope = cloneNode(_n.getQualifier(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        Name r = new Name(
                _n.getRange().orElse(null),
                scope,
                _n.getIdentifier()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SimpleName n, Object arg) {
        return new SimpleName(n.getIdentifier());
    }

    @Override
    public Visitable visit(ThisExpr _n, Object _arg) {
        Expression classExpr = cloneNode(_n.getClassExpr(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ThisExpr r = new ThisExpr(
                _n.getRange().orElse(null),
                classExpr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SuperExpr _n, Object _arg) {
        Expression classExpr = cloneNode(_n.getClassExpr(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SuperExpr r = new SuperExpr(
                _n.getRange().orElse(null),
                classExpr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(UnaryExpr _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        UnaryExpr r = new UnaryExpr(
                _n.getRange().orElse(null),
                expr, _n.getOperator()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(VariableDeclarationExpr _n, Object _arg) {
        NodeList<AnnotationExpr> annotations = cloneList(_n.getAnnotations(), _arg);
        NodeList<VariableDeclarator> variables_ = cloneList(_n.getVariables(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        VariableDeclarationExpr r = new VariableDeclarationExpr(
                _n.getRange().orElse(null),
                _n.getModifiers(),
                annotations,
                variables_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MarkerAnnotationExpr _n, Object _arg) {
        Name name = cloneNode(_n.getName(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        MarkerAnnotationExpr r = new MarkerAnnotationExpr(
                _n.getRange().orElse(null),
                name
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SingleMemberAnnotationExpr _n, Object _arg) {
        Name name = cloneNode(_n.getName(), _arg);
        Expression memberValue = cloneNode(_n.getMemberValue(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(
                _n.getRange().orElse(null),
                name, memberValue
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NormalAnnotationExpr _n, Object _arg) {
        Name name = cloneNode(_n.getName(), _arg);
        NodeList<MemberValuePair> pairs = cloneList(_n.getPairs(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        NormalAnnotationExpr r = new NormalAnnotationExpr(
                _n.getRange().orElse(null),
                name, pairs
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MemberValuePair _n, Object _arg) {
        Expression value = cloneNode(_n.getValue(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        MemberValuePair r = new MemberValuePair(
                _n.getRange().orElse(null),
                _n.getName(), value
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ExplicitConstructorInvocationStmt _n, Object _arg) {
        NodeList<Type> typeArguments_ = cloneList(_n.getTypeArguments().orElse(null), _arg);
        Expression expr_ = cloneNode(_n.getExpression(), _arg);
        NodeList<Expression> args = cloneList(_n.getArguments(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(
                _n.getRange().orElse(null),
                typeArguments_,
                _n.isThis(),
                expr_,
                args
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LocalClassDeclarationStmt _n, Object _arg) {
        ClassOrInterfaceDeclaration typeDecl = cloneNode(_n.getClassDeclaration(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        LocalClassDeclarationStmt r = new LocalClassDeclarationStmt(
                _n.getRange().orElse(null),
                typeDecl
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AssertStmt _n, Object _arg) {
        Expression check = cloneNode(_n.getCheck(), _arg);
        Expression message = cloneNode(_n.getMessage(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        AssertStmt r = new AssertStmt(
                _n.getRange().orElse(null),
                check, message
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BlockStmt _n, Object _arg) {
        NodeList<Statement> stmts = cloneList(_n.getStatements(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        BlockStmt r = new BlockStmt(
                _n.getRange().orElse(null),
                stmts
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LabeledStmt _n, Object _arg) {
        Statement stmt = cloneNode(_n.getStatement(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        LabeledStmt r = new LabeledStmt(
                _n.getRange().orElse(null),
                _n.getLabel(), stmt
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EmptyStmt _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        EmptyStmt r = new EmptyStmt(_n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ExpressionStmt _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ExpressionStmt r = new ExpressionStmt(
                _n.getRange().orElse(null),
                expr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SwitchStmt _n, Object _arg) {
        Expression selector = cloneNode(_n.getSelector(), _arg);
        NodeList<SwitchEntryStmt> entries = cloneList(_n.getEntries(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SwitchStmt r = new SwitchStmt(
                _n.getRange().orElse(null),
                selector, entries
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SwitchEntryStmt _n, Object _arg) {
        Expression label = cloneNode(_n.getLabel(), _arg);
        NodeList<Statement> stmts = cloneList(_n.getStatements(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SwitchEntryStmt r = new SwitchEntryStmt(
                _n.getRange().orElse(null),
                label, stmts
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BreakStmt _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        BreakStmt r = new BreakStmt(
                _n.getRange().orElse(null),
                _n.getIdentifier().orElse(null)
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ReturnStmt _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ReturnStmt r = new ReturnStmt(
                _n.getRange().orElse(null),
                expr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IfStmt _n, Object _arg) {
        Expression condition = cloneNode(_n.getCondition(), _arg);
        Statement thenStmt = cloneNode(_n.getThenStmt(), _arg);
        Statement elseStmt = cloneNode(_n.getElseStmt(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        IfStmt r = new IfStmt(
                _n.getRange().orElse(null),
                condition, thenStmt, elseStmt
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(WhileStmt _n, Object _arg) {
        Expression condition = cloneNode(_n.getCondition(), _arg);
        Statement body = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        WhileStmt r = new WhileStmt(
                _n.getRange().orElse(null),
                condition, body
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ContinueStmt _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);

        ContinueStmt r = new ContinueStmt(
                _n.getRange().orElse(null),
                _n.getIdentifier().orElse(null)
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(DoStmt _n, Object _arg) {
        Statement body = cloneNode(_n.getBody(), _arg);
        Expression condition = cloneNode(_n.getCondition(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        DoStmt r = new DoStmt(
                _n.getRange().orElse(null),
                body, condition
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ForeachStmt _n, Object _arg) {
        VariableDeclarationExpr var = cloneNode(_n.getVariable(), _arg);
        Expression iterable = cloneNode(_n.getIterable(), _arg);
        Statement body = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ForeachStmt r = new ForeachStmt(
                _n.getRange().orElse(null),
                var, iterable, body
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ForStmt _n, Object _arg) {
        NodeList<Expression> init = cloneList(_n.getInitialization(), _arg);
        Expression compare = cloneNode(_n.getCompare(), _arg);
        NodeList<Expression> update = cloneList(_n.getUpdate(), _arg);
        Statement body = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ForStmt r = new ForStmt(
                _n.getRange().orElse(null),
                init, compare, update, body
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ThrowStmt _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        ThrowStmt r = new ThrowStmt(
                _n.getRange().orElse(null),
                expr
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SynchronizedStmt _n, Object _arg) {
        Expression expr = cloneNode(_n.getExpression(), _arg);
        BlockStmt block = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SynchronizedStmt r = new SynchronizedStmt(
                _n.getRange().orElse(null),
                expr, block
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TryStmt _n, Object _arg) {
        NodeList<VariableDeclarationExpr> resources = cloneList(_n.getResources(), _arg);
        BlockStmt tryBlock = cloneNode(_n.getTryBlock(), _arg);
        NodeList<CatchClause> catchs = cloneList(_n.getCatchClauses(), _arg);
        BlockStmt finallyBlock = cloneNode(_n.getFinallyBlock(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        TryStmt r = new TryStmt(
                _n.getRange().orElse(null),
                resources, tryBlock, catchs, finallyBlock
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CatchClause _n, Object _arg) {
        Parameter param = cloneNode(_n.getParameter(), _arg);
        BlockStmt catchBlock = cloneNode(_n.getBody(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        CatchClause r = new CatchClause(_n.getRange().orElse(null), param, catchBlock);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LambdaExpr _n, Object _arg) {
        NodeList<Parameter> lambdaParameters = cloneList(_n.getParameters(), _arg);

        Statement body = cloneNode(_n.getBody(), _arg);

        return new LambdaExpr(_n.getRange().orElse(null), lambdaParameters, body,
                _n.isEnclosingParameters());
    }

    @Override
    public Visitable visit(MethodReferenceExpr _n, Object arg) {

        Expression scope = cloneNode(_n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(_n.getTypeArguments().orElse(null), arg);

        return new MethodReferenceExpr(_n.getRange().orElse(null), scope,
                typeArguments, _n.getIdentifier());
    }

    @Override
    public Visitable visit(TypeExpr n, Object arg) {

        Type t = cloneNode(n.getType(), arg);

        return new TypeExpr(n.getRange().orElse(null), t);
    }

    @Override
    public Visitable visit(NodeList n, Object arg) {
        NodeList<Node> newNodes = new NodeList<>(null);
        for (Object node : n) {
            Node resultNode = (Node) ((Node) node).accept(this, arg);
            if (resultNode != null) {
                newNodes.add(resultNode);
            }
        }
        return newNodes;
    }

    @Override
    public Visitable visit(BadImportDeclaration _n, Object _arg) {
        Comment comment = cloneNode(_n.getComment(), _arg);
        return new BadImportDeclaration(_n.getRange().orElse(null)).setComment(comment);
    }

    @Override
    public Visitable visit(SingleStaticImportDeclaration _n, Object _arg) {
        ClassOrInterfaceType type_ = cloneNode(_n.getType(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);


        SingleStaticImportDeclaration r = new SingleStaticImportDeclaration(
                _n.getRange().orElse(null),
                type_,
                _n.getStaticMember()
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SingleTypeImportDeclaration _n, Object _arg) {
        ClassOrInterfaceType type_ = cloneNode(_n.getType(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        SingleTypeImportDeclaration r = new SingleTypeImportDeclaration(
                _n.getRange().orElse(null),
                type_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(StaticImportOnDemandDeclaration _n, Object _arg) {
        ClassOrInterfaceType type_ = cloneNode(_n.getType(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        StaticImportOnDemandDeclaration r = new StaticImportOnDemandDeclaration(
                _n.getRange().orElse(null),
                type_
        );
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TypeImportOnDemandDeclaration _n, Object _arg) {
        Name name = cloneNode(_n.getName(), _arg);
        Comment comment = cloneNode(_n.getComment(), _arg);

        TypeImportOnDemandDeclaration r = new TypeImportOnDemandDeclaration(
                _n.getRange().orElse(null),
                name
        );
        r.setComment(comment);
        return r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNode(Optional<T> _node, Object _arg) {
        if (!_node.isPresent()) {
            return null;
        }
        Node r = (Node) _node.get().accept(this, _arg);
        if (r == null) {
            return null;
        }
        return (T) r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNode(T _node, Object _arg) {
        if (_node == null) {
            return null;
        }
        Node r = (Node) _node.accept(this, _arg);
        if (r == null) {
            return null;
        }
        return (T) r;
    }

    private <N extends Node> NodeList<N> cloneList(NodeList<N> list, Object _arg) {
        if (list == null) {
            return null;
        }
        return (NodeList<N>) list.accept(this, _arg);
    }

}
