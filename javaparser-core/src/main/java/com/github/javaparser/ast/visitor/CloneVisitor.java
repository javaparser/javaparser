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
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import java.util.Optional;

/**
 * A visitor that clones (copies) a node and all its children.
 */
public class CloneVisitor implements GenericVisitor<Visitable, Void> {

    @Override
    public Visitable visit(CompilationUnit n, Void arg) {
        NodeList<ImportDeclaration> imports = cloneList(n.getImports(), arg);
        PackageDeclaration packageDeclaration = cloneNode(n.getPackageDeclaration(), arg);
        NodeList<TypeDeclaration<?>> types = cloneList(n.getTypes(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CompilationUnit r = new CompilationUnit(n.getRange().orElse(null), packageDeclaration, imports, types);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(PackageDeclaration n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        PackageDeclaration r = new PackageDeclaration(n.getRange().orElse(null), annotations, name);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TypeParameter n, Void arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<ClassOrInterfaceType> typeBound = cloneList(n.getTypeBound(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TypeParameter r = new TypeParameter(n.getRange().orElse(null), name, typeBound, annotations);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LineComment n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LineComment r = new LineComment(n.getRange().orElse(null), n.getContent());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BlockComment n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BlockComment r = new BlockComment(n.getRange().orElse(null), n.getContent());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ClassOrInterfaceDeclaration n, Void arg) {
        NodeList<ClassOrInterfaceType> extendedTypes = cloneList(n.getExtendedTypes(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, n.isInterface(), name, typeParameters, extendedTypes, implementedTypes, members);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnumDeclaration n, Void arg) {
        NodeList<EnumConstantDeclaration> entries = cloneList(n.getEntries(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnumDeclaration r = new EnumDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, name, implementedTypes, entries, members);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnumConstantDeclaration n, Void arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        NodeList<BodyDeclaration<?>> classBody = cloneList(n.getClassBody(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnumConstantDeclaration r = new EnumConstantDeclaration(n.getRange().orElse(null), annotations, name, arguments, classBody);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AnnotationDeclaration n, Void arg) {
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AnnotationDeclaration r = new AnnotationDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, name, members);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AnnotationMemberDeclaration n, Void arg) {
        Expression defaultValue = cloneNode(n.getDefaultValue(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, type, name, defaultValue);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(FieldDeclaration n, Void arg) {
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        FieldDeclaration r = new FieldDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, variables);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(VariableDeclarator n, Void arg) {
        Expression initializer = cloneNode(n.getInitializer(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VariableDeclarator r = new VariableDeclarator(n.getRange().orElse(null), type, name, initializer);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ConstructorDeclaration n, Void arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ConstructorDeclaration r = new ConstructorDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, typeParameters, name, parameters, thrownExceptions, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MethodDeclaration n, Void arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        Type type = cloneNode(n.getType(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodDeclaration r = new MethodDeclaration(n.getRange().orElse(null), n.getModifiers(), annotations, typeParameters, type, name, n.isDefault(), parameters, thrownExceptions, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(Parameter n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        Parameter r = new Parameter(n.getRange().orElse(null), n.getModifiers(), annotations, type, n.isVarArgs(), name);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EmptyMemberDeclaration n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EmptyMemberDeclaration r = new EmptyMemberDeclaration(n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(InitializerDeclaration n, Void arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        InitializerDeclaration r = new InitializerDeclaration(n.getRange().orElse(null), n.isStatic(), body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(JavadocComment n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        JavadocComment r = new JavadocComment(n.getRange().orElse(null), n.getContent());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ClassOrInterfaceType n, Void arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        ClassOrInterfaceType scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassOrInterfaceType r = new ClassOrInterfaceType(n.getRange().orElse(null), scope, name, typeArguments);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(PrimitiveType n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        PrimitiveType r = new PrimitiveType(n.getRange().orElse(null), n.getType());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayType n, Void arg) {
        Type componentType = cloneNode(n.getComponentType(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayType r = new ArrayType(n.getRange().orElse(null), componentType, annotations);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayCreationLevel n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Expression dimension = cloneNode(n.getDimension(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayCreationLevel r = new ArrayCreationLevel(n.getRange().orElse(null), dimension, annotations);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IntersectionType n, Void arg) {
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        IntersectionType r = new IntersectionType(n.getRange().orElse(null), elements);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(UnionType n, Void arg) {
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnionType r = new UnionType(n.getRange().orElse(null), elements);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(VoidType n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VoidType r = new VoidType(n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(WildcardType n, Void arg) {
        ReferenceType extendedTypes = cloneNode(n.getExtendedTypes(), arg);
        ReferenceType superTypes = cloneNode(n.getSuperTypes(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        WildcardType r = new WildcardType(n.getRange().orElse(null), extendedTypes, superTypes);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(UnknownType n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnknownType r = new UnknownType(n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayAccessExpr n, Void arg) {
        Expression index = cloneNode(n.getIndex(), arg);
        Expression name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayAccessExpr r = new ArrayAccessExpr(n.getRange().orElse(null), name, index);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayCreationExpr n, Void arg) {
        Type elementType = cloneNode(n.getElementType(), arg);
        ArrayInitializerExpr initializer = cloneNode(n.getInitializer(), arg);
        NodeList<ArrayCreationLevel> levels = cloneList(n.getLevels(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayCreationExpr r = new ArrayCreationExpr(n.getRange().orElse(null), elementType, levels, initializer);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ArrayInitializerExpr n, Void arg) {
        NodeList<Expression> values = cloneList(n.getValues(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayInitializerExpr r = new ArrayInitializerExpr(n.getRange().orElse(null), values);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AssignExpr n, Void arg) {
        Expression target = cloneNode(n.getTarget(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AssignExpr r = new AssignExpr(n.getRange().orElse(null), target, value, n.getOperator());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BinaryExpr n, Void arg) {
        Expression left = cloneNode(n.getLeft(), arg);
        Expression right = cloneNode(n.getRight(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BinaryExpr r = new BinaryExpr(n.getRange().orElse(null), left, right, n.getOperator());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CastExpr n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CastExpr r = new CastExpr(n.getRange().orElse(null), type, expression);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ClassExpr n, Void arg) {
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassExpr r = new ClassExpr(n.getRange().orElse(null), type);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ConditionalExpr n, Void arg) {
        Expression condition = cloneNode(n.getCondition(), arg);
        Expression elseExpr = cloneNode(n.getElseExpr(), arg);
        Expression thenExpr = cloneNode(n.getThenExpr(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ConditionalExpr r = new ConditionalExpr(n.getRange().orElse(null), condition, thenExpr, elseExpr);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EnclosedExpr n, Void arg) {
        Expression inner = cloneNode(n.getInner(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnclosedExpr r = new EnclosedExpr(n.getRange().orElse(null), inner);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(FieldAccessExpr n, Void arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        FieldAccessExpr r = new FieldAccessExpr(n.getRange().orElse(null), scope, typeArguments, name);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(InstanceOfExpr n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        ReferenceType<?> type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        InstanceOfExpr r = new InstanceOfExpr(n.getRange().orElse(null), expression, type);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(StringLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        StringLiteralExpr r = new StringLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IntegerLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        IntegerLiteralExpr r = new IntegerLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LongLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LongLiteralExpr r = new LongLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CharLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        CharLiteralExpr r = new CharLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(DoubleLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        DoubleLiteralExpr r = new DoubleLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BooleanLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BooleanLiteralExpr r = new BooleanLiteralExpr(n.getRange().orElse(null), n.getValue());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NullLiteralExpr n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NullLiteralExpr r = new NullLiteralExpr(n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MethodCallExpr n, Void arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodCallExpr r = new MethodCallExpr(n.getRange().orElse(null), scope, typeArguments, name, arguments);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NameExpr n, Void arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        NameExpr r = new NameExpr(n.getRange().orElse(null), name);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ObjectCreationExpr n, Void arg) {
        NodeList<BodyDeclaration<?>> anonymousClassBody = cloneList(n.getAnonymousClassBody().orElse(null), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        ClassOrInterfaceType type = cloneNode(n.getType(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ObjectCreationExpr r = new ObjectCreationExpr(n.getRange().orElse(null), scope, type, typeArguments, arguments, anonymousClassBody);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(Name n, Void arg) {
        Name qualifier = cloneNode(n.getQualifier(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        Name r = new Name(n.getRange().orElse(null), qualifier, n.getIdentifier());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SimpleName n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName r = new SimpleName(n.getRange().orElse(null), n.getIdentifier());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ThisExpr n, Void arg) {
        Expression classExpr = cloneNode(n.getClassExpr(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ThisExpr r = new ThisExpr(n.getRange().orElse(null), classExpr);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SuperExpr n, Void arg) {
        Expression classExpr = cloneNode(n.getClassExpr(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SuperExpr r = new SuperExpr(n.getRange().orElse(null), classExpr);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(UnaryExpr n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnaryExpr r = new UnaryExpr(n.getRange().orElse(null), expression, n.getOperator());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(VariableDeclarationExpr n, Void arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VariableDeclarationExpr r = new VariableDeclarationExpr(n.getRange().orElse(null), n.getModifiers(), annotations, variables);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MarkerAnnotationExpr n, Void arg) {
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MarkerAnnotationExpr r = new MarkerAnnotationExpr(n.getRange().orElse(null), name);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SingleMemberAnnotationExpr n, Void arg) {
        Expression memberValue = cloneNode(n.getMemberValue(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(n.getRange().orElse(null), name, memberValue);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NormalAnnotationExpr n, Void arg) {
        NodeList<MemberValuePair> pairs = cloneList(n.getPairs(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        NormalAnnotationExpr r = new NormalAnnotationExpr(n.getRange().orElse(null), name, pairs);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MemberValuePair n, Void arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MemberValuePair r = new MemberValuePair(n.getRange().orElse(null), name, value);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ExplicitConstructorInvocationStmt n, Void arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(n.getRange().orElse(null), typeArguments, n.isThis(), expression, arguments);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LocalClassDeclarationStmt n, Void arg) {
        ClassOrInterfaceDeclaration classDeclaration = cloneNode(n.getClassDeclaration(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LocalClassDeclarationStmt r = new LocalClassDeclarationStmt(n.getRange().orElse(null), classDeclaration);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(AssertStmt n, Void arg) {
        Expression check = cloneNode(n.getCheck(), arg);
        Expression message = cloneNode(n.getMessage(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AssertStmt r = new AssertStmt(n.getRange().orElse(null), check, message);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BlockStmt n, Void arg) {
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BlockStmt r = new BlockStmt(n.getRange().orElse(null), statements);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LabeledStmt n, Void arg) {
        SimpleName label = cloneNode(n.getLabel(), arg);
        Statement statement = cloneNode(n.getStatement(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LabeledStmt r = new LabeledStmt(n.getRange().orElse(null), label, statement);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(EmptyStmt n, Void arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        EmptyStmt r = new EmptyStmt(n.getRange().orElse(null));
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ExpressionStmt n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ExpressionStmt r = new ExpressionStmt(n.getRange().orElse(null), expression);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SwitchStmt n, Void arg) {
        NodeList<SwitchEntryStmt> entries = cloneList(n.getEntries(), arg);
        Expression selector = cloneNode(n.getSelector(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SwitchStmt r = new SwitchStmt(n.getRange().orElse(null), selector, entries);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SwitchEntryStmt n, Void arg) {
        Expression label = cloneNode(n.getLabel(), arg);
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SwitchEntryStmt r = new SwitchEntryStmt(n.getRange().orElse(null), label, statements);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(BreakStmt n, Void arg) {
        SimpleName label = cloneNode(n.getLabel(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BreakStmt r = new BreakStmt(n.getRange().orElse(null), label);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ReturnStmt n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ReturnStmt r = new ReturnStmt(n.getRange().orElse(null), expression);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(IfStmt n, Void arg) {
        Expression condition = cloneNode(n.getCondition(), arg);
        Statement elseStmt = cloneNode(n.getElseStmt(), arg);
        Statement thenStmt = cloneNode(n.getThenStmt(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        IfStmt r = new IfStmt(n.getRange().orElse(null), condition, thenStmt, elseStmt);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(WhileStmt n, Void arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        WhileStmt r = new WhileStmt(n.getRange().orElse(null), condition, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ContinueStmt n, Void arg) {
        SimpleName label = cloneNode(n.getLabel(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ContinueStmt r = new ContinueStmt(n.getRange().orElse(null), label);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(DoStmt n, Void arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        DoStmt r = new DoStmt(n.getRange().orElse(null), body, condition);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ForeachStmt n, Void arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression iterable = cloneNode(n.getIterable(), arg);
        VariableDeclarationExpr variable = cloneNode(n.getVariable(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ForeachStmt r = new ForeachStmt(n.getRange().orElse(null), variable, iterable, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ForStmt n, Void arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression compare = cloneNode(n.getCompare(), arg);
        NodeList<Expression> initialization = cloneList(n.getInitialization(), arg);
        NodeList<Expression> update = cloneList(n.getUpdate(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ForStmt r = new ForStmt(n.getRange().orElse(null), initialization, compare, update, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(ThrowStmt n, Void arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ThrowStmt r = new ThrowStmt(n.getRange().orElse(null), expression);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(SynchronizedStmt n, Void arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SynchronizedStmt r = new SynchronizedStmt(n.getRange().orElse(null), expression, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TryStmt n, Void arg) {
        NodeList<CatchClause> catchClauses = cloneList(n.getCatchClauses(), arg);
        BlockStmt finallyBlock = cloneNode(n.getFinallyBlock(), arg);
        NodeList<VariableDeclarationExpr> resources = cloneList(n.getResources(), arg);
        BlockStmt tryBlock = cloneNode(n.getTryBlock(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TryStmt r = new TryStmt(n.getRange().orElse(null), resources, tryBlock, catchClauses, finallyBlock);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(CatchClause n, Void arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        Parameter parameter = cloneNode(n.getParameter(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CatchClause r = new CatchClause(n.getRange().orElse(null), parameter, body);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(LambdaExpr n, Void arg) {
        Statement body = cloneNode(n.getBody(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LambdaExpr r = new LambdaExpr(n.getRange().orElse(null), parameters, body, n.isEnclosingParameters());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(MethodReferenceExpr n, Void arg) {
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodReferenceExpr r = new MethodReferenceExpr(n.getRange().orElse(null), scope, typeArguments, n.getIdentifier());
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(TypeExpr n, Void arg) {
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TypeExpr r = new TypeExpr(n.getRange().orElse(null), type);
        r.setComment(comment);
        return r;
    }

    @Override
    public Visitable visit(NodeList n, Void arg) {
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
    public Visitable visit(ImportDeclaration n, Void arg) {
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ImportDeclaration r = new ImportDeclaration(n.getRange().orElse(null), name, n.isStatic(), n.isAsterisk());
        r.setComment(comment);
        return r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNode(Optional<T> _node, Void _arg) {
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
    protected <T extends Node> T cloneNode(T _node, Void _arg) {
        if (_node == null) {
            return null;
        }
        Node r = (Node) _node.accept(this, _arg);
        if (r == null) {
            return null;
        }
        return (T) r;
    }

    private <N extends Node> NodeList<N> cloneList(NodeList<N> list, Void _arg) {
        if (list == null) {
            return null;
        }
        return (NodeList<N>) list.accept(this, _arg);
    }
}

