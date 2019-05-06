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
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import java.util.Optional;

/**
 * A visitor that clones (copies) a node and all its children.
 */
public class CloneVisitor implements GenericVisitor<Visitable, Object> {

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.CloneVisitorGenerator")
    public Visitable visit(final CompilationUnit n, final Object arg) {
        NodeList<ImportDeclaration> imports = cloneList(n.getImports(), arg);
        ModuleDeclaration module = cloneNode(n.getModule(), arg);
        PackageDeclaration packageDeclaration = cloneNode(n.getPackageDeclaration(), arg);
        NodeList<TypeDeclaration<?>> types = cloneList(n.getTypes(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CompilationUnit r = new CompilationUnit(n.getTokenRange().orElse(null), packageDeclaration, imports, types, module);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.CloneVisitorGenerator")
    public Visitable visit(final PackageDeclaration n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        PackageDeclaration r = new PackageDeclaration(n.getTokenRange().orElse(null), annotations, name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TypeParameter n, final Object arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<ClassOrInterfaceType> typeBound = cloneList(n.getTypeBound(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TypeParameter r = new TypeParameter(n.getTokenRange().orElse(null), name, typeBound, annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LineComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LineComment r = new LineComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BlockComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BlockComment r = new BlockComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceDeclaration n, final Object arg) {
        NodeList<ClassOrInterfaceType> extendedTypes = cloneList(n.getExtendedTypes(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, n.isInterface(), name, typeParameters, extendedTypes, implementedTypes, members);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnumDeclaration n, final Object arg) {
        NodeList<EnumConstantDeclaration> entries = cloneList(n.getEntries(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnumDeclaration r = new EnumDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, name, implementedTypes, entries, members);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnumConstantDeclaration n, final Object arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        NodeList<BodyDeclaration<?>> classBody = cloneList(n.getClassBody(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnumConstantDeclaration r = new EnumConstantDeclaration(n.getTokenRange().orElse(null), annotations, name, arguments, classBody);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AnnotationDeclaration n, final Object arg) {
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AnnotationDeclaration r = new AnnotationDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, name, members);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AnnotationMemberDeclaration n, final Object arg) {
        Expression defaultValue = cloneNode(n.getDefaultValue(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, type, name, defaultValue);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final FieldDeclaration n, final Object arg) {
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        FieldDeclaration r = new FieldDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, variables);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VariableDeclarator n, final Object arg) {
        Expression initializer = cloneNode(n.getInitializer(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VariableDeclarator r = new VariableDeclarator(n.getTokenRange().orElse(null), type, name, initializer);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ConstructorDeclaration n, final Object arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        ReceiverParameter receiverParameter = cloneNode(n.getReceiverParameter(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ConstructorDeclaration r = new ConstructorDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, typeParameters, name, parameters, thrownExceptions, body, receiverParameter);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodDeclaration n, final Object arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        Type type = cloneNode(n.getType(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        ReceiverParameter receiverParameter = cloneNode(n.getReceiverParameter(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodDeclaration r = new MethodDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, typeParameters, type, name, parameters, thrownExceptions, body, receiverParameter);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Parameter n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        NodeList<AnnotationExpr> varArgsAnnotations = cloneList(n.getVarArgsAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        Parameter r = new Parameter(n.getTokenRange().orElse(null), modifiers, annotations, type, n.isVarArgs(), varArgsAnnotations, name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final InitializerDeclaration n, final Object arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        InitializerDeclaration r = new InitializerDeclaration(n.getTokenRange().orElse(null), n.isStatic(), body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final JavadocComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        JavadocComment r = new JavadocComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceType n, final Object arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        ClassOrInterfaceType scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassOrInterfaceType r = new ClassOrInterfaceType(n.getTokenRange().orElse(null), scope, name, typeArguments, annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final PrimitiveType n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        PrimitiveType r = new PrimitiveType(n.getTokenRange().orElse(null), n.getType(), annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayType n, final Object arg) {
        Type componentType = cloneNode(n.getComponentType(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayType r = new ArrayType(n.getTokenRange().orElse(null), componentType, n.getOrigin(), annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayCreationLevel n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Expression dimension = cloneNode(n.getDimension(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayCreationLevel r = new ArrayCreationLevel(n.getTokenRange().orElse(null), dimension, annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IntersectionType n, final Object arg) {
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        IntersectionType r = new IntersectionType(n.getTokenRange().orElse(null), elements);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnionType n, final Object arg) {
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnionType r = new UnionType(n.getTokenRange().orElse(null), elements);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VoidType n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VoidType r = new VoidType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final WildcardType n, final Object arg) {
        ReferenceType extendedType = cloneNode(n.getExtendedType(), arg);
        ReferenceType superType = cloneNode(n.getSuperType(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        WildcardType r = new WildcardType(n.getTokenRange().orElse(null), extendedType, superType, annotations);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnknownType n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnknownType r = new UnknownType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayAccessExpr n, final Object arg) {
        Expression index = cloneNode(n.getIndex(), arg);
        Expression name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayAccessExpr r = new ArrayAccessExpr(n.getTokenRange().orElse(null), name, index);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayCreationExpr n, final Object arg) {
        Type elementType = cloneNode(n.getElementType(), arg);
        ArrayInitializerExpr initializer = cloneNode(n.getInitializer(), arg);
        NodeList<ArrayCreationLevel> levels = cloneList(n.getLevels(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayCreationExpr r = new ArrayCreationExpr(n.getTokenRange().orElse(null), elementType, levels, initializer);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayInitializerExpr n, final Object arg) {
        NodeList<Expression> values = cloneList(n.getValues(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ArrayInitializerExpr r = new ArrayInitializerExpr(n.getTokenRange().orElse(null), values);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AssignExpr n, final Object arg) {
        Expression target = cloneNode(n.getTarget(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AssignExpr r = new AssignExpr(n.getTokenRange().orElse(null), target, value, n.getOperator());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BinaryExpr n, final Object arg) {
        Expression left = cloneNode(n.getLeft(), arg);
        Expression right = cloneNode(n.getRight(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BinaryExpr r = new BinaryExpr(n.getTokenRange().orElse(null), left, right, n.getOperator());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CastExpr n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CastExpr r = new CastExpr(n.getTokenRange().orElse(null), type, expression);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassExpr n, final Object arg) {
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ClassExpr r = new ClassExpr(n.getTokenRange().orElse(null), type);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ConditionalExpr n, final Object arg) {
        Expression condition = cloneNode(n.getCondition(), arg);
        Expression elseExpr = cloneNode(n.getElseExpr(), arg);
        Expression thenExpr = cloneNode(n.getThenExpr(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ConditionalExpr r = new ConditionalExpr(n.getTokenRange().orElse(null), condition, thenExpr, elseExpr);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnclosedExpr n, final Object arg) {
        Expression inner = cloneNode(n.getInner(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        EnclosedExpr r = new EnclosedExpr(n.getTokenRange().orElse(null), inner);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final FieldAccessExpr n, final Object arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        FieldAccessExpr r = new FieldAccessExpr(n.getTokenRange().orElse(null), scope, typeArguments, name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final InstanceOfExpr n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        ReferenceType type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        InstanceOfExpr r = new InstanceOfExpr(n.getTokenRange().orElse(null), expression, type);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final StringLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        StringLiteralExpr r = new StringLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IntegerLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        IntegerLiteralExpr r = new IntegerLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LongLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LongLiteralExpr r = new LongLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CharLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        CharLiteralExpr r = new CharLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final DoubleLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        DoubleLiteralExpr r = new DoubleLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BooleanLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BooleanLiteralExpr r = new BooleanLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NullLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NullLiteralExpr r = new NullLiteralExpr(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodCallExpr n, final Object arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodCallExpr r = new MethodCallExpr(n.getTokenRange().orElse(null), scope, typeArguments, name, arguments);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NameExpr n, final Object arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        NameExpr r = new NameExpr(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ObjectCreationExpr n, final Object arg) {
        NodeList<BodyDeclaration<?>> anonymousClassBody = cloneList(n.getAnonymousClassBody().orElse(null), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        ClassOrInterfaceType type = cloneNode(n.getType(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ObjectCreationExpr r = new ObjectCreationExpr(n.getTokenRange().orElse(null), scope, type, typeArguments, arguments, anonymousClassBody);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Name n, final Object arg) {
        Name qualifier = cloneNode(n.getQualifier(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        Name r = new Name(n.getTokenRange().orElse(null), qualifier, n.getIdentifier());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SimpleName n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName r = new SimpleName(n.getTokenRange().orElse(null), n.getIdentifier());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ThisExpr n, final Object arg) {
        Name typeName = cloneNode(n.getTypeName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ThisExpr r = new ThisExpr(n.getTokenRange().orElse(null), typeName);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SuperExpr n, final Object arg) {
        Name typeName = cloneNode(n.getTypeName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SuperExpr r = new SuperExpr(n.getTokenRange().orElse(null), typeName);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnaryExpr n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        UnaryExpr r = new UnaryExpr(n.getTokenRange().orElse(null), expression, n.getOperator());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VariableDeclarationExpr n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VariableDeclarationExpr r = new VariableDeclarationExpr(n.getTokenRange().orElse(null), modifiers, annotations, variables);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MarkerAnnotationExpr n, final Object arg) {
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MarkerAnnotationExpr r = new MarkerAnnotationExpr(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SingleMemberAnnotationExpr n, final Object arg) {
        Expression memberValue = cloneNode(n.getMemberValue(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(n.getTokenRange().orElse(null), name, memberValue);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NormalAnnotationExpr n, final Object arg) {
        NodeList<MemberValuePair> pairs = cloneList(n.getPairs(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        NormalAnnotationExpr r = new NormalAnnotationExpr(n.getTokenRange().orElse(null), name, pairs);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MemberValuePair n, final Object arg) {
        SimpleName name = cloneNode(n.getName(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MemberValuePair r = new MemberValuePair(n.getTokenRange().orElse(null), name, value);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ExplicitConstructorInvocationStmt n, final Object arg) {
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(n.getTokenRange().orElse(null), typeArguments, n.isThis(), expression, arguments);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LocalClassDeclarationStmt n, final Object arg) {
        ClassOrInterfaceDeclaration classDeclaration = cloneNode(n.getClassDeclaration(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LocalClassDeclarationStmt r = new LocalClassDeclarationStmt(n.getTokenRange().orElse(null), classDeclaration);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AssertStmt n, final Object arg) {
        Expression check = cloneNode(n.getCheck(), arg);
        Expression message = cloneNode(n.getMessage(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        AssertStmt r = new AssertStmt(n.getTokenRange().orElse(null), check, message);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BlockStmt n, final Object arg) {
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BlockStmt r = new BlockStmt(n.getTokenRange().orElse(null), statements);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LabeledStmt n, final Object arg) {
        SimpleName label = cloneNode(n.getLabel(), arg);
        Statement statement = cloneNode(n.getStatement(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LabeledStmt r = new LabeledStmt(n.getTokenRange().orElse(null), label, statement);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EmptyStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        EmptyStmt r = new EmptyStmt(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ExpressionStmt n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ExpressionStmt r = new ExpressionStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchStmt n, final Object arg) {
        NodeList<SwitchEntry> entries = cloneList(n.getEntries(), arg);
        Expression selector = cloneNode(n.getSelector(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SwitchStmt r = new SwitchStmt(n.getTokenRange().orElse(null), selector, entries);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchEntry n, final Object arg) {
        NodeList<Expression> labels = cloneList(n.getLabels(), arg);
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SwitchEntry r = new SwitchEntry(n.getTokenRange().orElse(null), labels, n.getType(), statements);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BreakStmt n, final Object arg) {
        Expression value = cloneNode(n.getValue(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        BreakStmt r = new BreakStmt(n.getTokenRange().orElse(null), value);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ReturnStmt n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ReturnStmt r = new ReturnStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IfStmt n, final Object arg) {
        Expression condition = cloneNode(n.getCondition(), arg);
        Statement elseStmt = cloneNode(n.getElseStmt(), arg);
        Statement thenStmt = cloneNode(n.getThenStmt(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        IfStmt r = new IfStmt(n.getTokenRange().orElse(null), condition, thenStmt, elseStmt);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final WhileStmt n, final Object arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        WhileStmt r = new WhileStmt(n.getTokenRange().orElse(null), condition, body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ContinueStmt n, final Object arg) {
        SimpleName label = cloneNode(n.getLabel(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ContinueStmt r = new ContinueStmt(n.getTokenRange().orElse(null), label);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final DoStmt n, final Object arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        DoStmt r = new DoStmt(n.getTokenRange().orElse(null), body, condition);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ForEachStmt n, final Object arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression iterable = cloneNode(n.getIterable(), arg);
        VariableDeclarationExpr variable = cloneNode(n.getVariable(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ForEachStmt r = new ForEachStmt(n.getTokenRange().orElse(null), variable, iterable, body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ForStmt n, final Object arg) {
        Statement body = cloneNode(n.getBody(), arg);
        Expression compare = cloneNode(n.getCompare(), arg);
        NodeList<Expression> initialization = cloneList(n.getInitialization(), arg);
        NodeList<Expression> update = cloneList(n.getUpdate(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ForStmt r = new ForStmt(n.getTokenRange().orElse(null), initialization, compare, update, body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ThrowStmt n, final Object arg) {
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ThrowStmt r = new ThrowStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SynchronizedStmt n, final Object arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SynchronizedStmt r = new SynchronizedStmt(n.getTokenRange().orElse(null), expression, body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TryStmt n, final Object arg) {
        NodeList<CatchClause> catchClauses = cloneList(n.getCatchClauses(), arg);
        BlockStmt finallyBlock = cloneNode(n.getFinallyBlock(), arg);
        NodeList<Expression> resources = cloneList(n.getResources(), arg);
        BlockStmt tryBlock = cloneNode(n.getTryBlock(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TryStmt r = new TryStmt(n.getTokenRange().orElse(null), resources, tryBlock, catchClauses, finallyBlock);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CatchClause n, final Object arg) {
        BlockStmt body = cloneNode(n.getBody(), arg);
        Parameter parameter = cloneNode(n.getParameter(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        CatchClause r = new CatchClause(n.getTokenRange().orElse(null), parameter, body);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LambdaExpr n, final Object arg) {
        Statement body = cloneNode(n.getBody(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        LambdaExpr r = new LambdaExpr(n.getTokenRange().orElse(null), parameters, body, n.isEnclosingParameters());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodReferenceExpr n, final Object arg) {
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        MethodReferenceExpr r = new MethodReferenceExpr(n.getTokenRange().orElse(null), scope, typeArguments, n.getIdentifier());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TypeExpr n, final Object arg) {
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        TypeExpr r = new TypeExpr(n.getTokenRange().orElse(null), type);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(NodeList n, Object arg) {
        NodeList<Node> newNodes = new NodeList<>();
        for (Object node : n) {
            Node resultNode = (Node) ((Node) node).accept(this, arg);
            if (resultNode != null) {
                newNodes.add(resultNode);
            }
        }
        return newNodes;
    }

    @Override
    public Node visit(final ImportDeclaration n, final Object arg) {
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ImportDeclaration r = new ImportDeclaration(n.getTokenRange().orElse(null), name, n.isStatic(), n.isAsterisk());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleDeclaration n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<ModuleDirective> directives = cloneList(n.getDirectives(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleDeclaration r = new ModuleDeclaration(n.getTokenRange().orElse(null), annotations, name, n.isOpen(), directives);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleRequiresDirective n, final Object arg) {
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleRequiresDirective r = new ModuleRequiresDirective(n.getTokenRange().orElse(null), modifiers, name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNode(Optional<T> node, Object arg) {
        if (!node.isPresent()) {
            return null;
        }
        Node r = (Node) node.get().accept(this, arg);
        if (r == null) {
            return null;
        }
        return (T) r;
    }

    @SuppressWarnings("unchecked")
    protected <T extends Node> T cloneNode(T node, Object arg) {
        if (node == null) {
            return null;
        }
        Node r = (Node) node.accept(this, arg);
        if (r == null) {
            return null;
        }
        return (T) r;
    }

    private <N extends Node> NodeList<N> cloneList(NodeList<N> list, Object arg) {
        if (list == null) {
            return null;
        }
        return (NodeList<N>) list.accept(this, arg);
    }

    @Override
    public Visitable visit(final ModuleExportsDirective n, final Object arg) {
        NodeList<Name> moduleNames = cloneList(n.getModuleNames(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleExportsDirective r = new ModuleExportsDirective(n.getTokenRange().orElse(null), name, moduleNames);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleProvidesDirective n, final Object arg) {
        Name name = cloneNode(n.getName(), arg);
        NodeList<Name> with = cloneList(n.getWith(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleProvidesDirective r = new ModuleProvidesDirective(n.getTokenRange().orElse(null), name, with);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleUsesDirective n, final Object arg) {
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleUsesDirective r = new ModuleUsesDirective(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleOpensDirective n, final Object arg) {
        NodeList<Name> moduleNames = cloneList(n.getModuleNames(), arg);
        Name name = cloneNode(n.getName(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ModuleOpensDirective r = new ModuleOpensDirective(n.getTokenRange().orElse(null), name, moduleNames);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnparsableStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        UnparsableStmt r = new UnparsableStmt(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ReceiverParameter n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Name name = cloneNode(n.getName(), arg);
        Type type = cloneNode(n.getType(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        ReceiverParameter r = new ReceiverParameter(n.getTokenRange().orElse(null), annotations, type, name);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VarType n, final Object arg) {
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        VarType r = new VarType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Modifier n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Modifier r = new Modifier(n.getTokenRange().orElse(null), n.getKeyword());
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchExpr n, final Object arg) {
        NodeList<SwitchEntry> entries = cloneList(n.getEntries(), arg);
        Expression selector = cloneNode(n.getSelector(), arg);
        Comment comment = cloneNode(n.getComment(), arg);
        SwitchExpr r = new SwitchExpr(n.getTokenRange().orElse(null), selector, entries);
        r.setComment(comment);
        copyData(n, r);
        return r;
    }

    private void copyData(Node source, Node destination) {
        for (DataKey dataKey : source.getDataKeys()) {
            destination.setData(dataKey, source.getData(dataKey));
        }
    }
}
