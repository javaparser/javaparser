/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<TypeDeclaration<?>> types = cloneList(n.getTypes(), arg);
        PackageDeclaration packageDeclaration = cloneNode(n.getPackageDeclaration(), arg);
        ModuleDeclaration module = cloneNode(n.getModule(), arg);
        NodeList<ImportDeclaration> imports = cloneList(n.getImports(), arg);
        CompilationUnit r = new CompilationUnit(n.getTokenRange().orElse(null), packageDeclaration, imports, types, module);
        n.getStorage().ifPresent(s -> r.setStorage(s.getPath(), s.getEncoding()));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.visitor.CloneVisitorGenerator")
    public Visitable visit(final PackageDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        PackageDeclaration r = new PackageDeclaration(n.getTokenRange().orElse(null), annotations, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TypeParameter n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<ClassOrInterfaceType> typeBound = cloneList(n.getTypeBound(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        TypeParameter r = new TypeParameter(n.getTokenRange().orElse(null), name, typeBound, annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LineComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LineComment r = new LineComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BlockComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BlockComment r = new BlockComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<ClassOrInterfaceType> extendedTypes = cloneList(n.getExtendedTypes(), arg);
        ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, n.isInterface(), name, typeParameters, extendedTypes, implementedTypes, members);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnumDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = cloneList(n.getImplementedTypes(), arg);
        NodeList<EnumConstantDeclaration> entries = cloneList(n.getEntries(), arg);
        EnumDeclaration r = new EnumDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, name, implementedTypes, entries, members);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnumConstantDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<BodyDeclaration<?>> classBody = cloneList(n.getClassBody(), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        EnumConstantDeclaration r = new EnumConstantDeclaration(n.getTokenRange().orElse(null), annotations, name, arguments, classBody);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AnnotationDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = cloneList(n.getMembers(), arg);
        AnnotationDeclaration r = new AnnotationDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, name, members);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AnnotationMemberDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Type type = cloneNode(n.getType(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        Expression defaultValue = cloneNode(n.getDefaultValue(), arg);
        AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, type, name, defaultValue);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final FieldDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        FieldDeclaration r = new FieldDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, variables);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VariableDeclarator n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Type type = cloneNode(n.getType(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        Expression initializer = cloneNode(n.getInitializer(), arg);
        VariableDeclarator r = new VariableDeclarator(n.getTokenRange().orElse(null), type, name, initializer);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ConstructorDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        ReceiverParameter receiverParameter = cloneNode(n.getReceiverParameter(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        BlockStmt body = cloneNode(n.getBody(), arg);
        ConstructorDeclaration r = new ConstructorDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, typeParameters, name, parameters, thrownExceptions, body, receiverParameter);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<TypeParameter> typeParameters = cloneList(n.getTypeParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = cloneList(n.getThrownExceptions(), arg);
        ReceiverParameter receiverParameter = cloneNode(n.getReceiverParameter(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        Type type = cloneNode(n.getType(), arg);
        BlockStmt body = cloneNode(n.getBody(), arg);
        MethodDeclaration r = new MethodDeclaration(n.getTokenRange().orElse(null), modifiers, annotations, typeParameters, type, name, parameters, thrownExceptions, body, receiverParameter);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Parameter n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> varArgsAnnotations = cloneList(n.getVarArgsAnnotations(), arg);
        Type type = cloneNode(n.getType(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Parameter r = new Parameter(n.getTokenRange().orElse(null), modifiers, annotations, type, n.isVarArgs(), varArgsAnnotations, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final InitializerDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        BlockStmt body = cloneNode(n.getBody(), arg);
        InitializerDeclaration r = new InitializerDeclaration(n.getTokenRange().orElse(null), n.isStatic(), body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final JavadocComment n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        JavadocComment r = new JavadocComment(n.getTokenRange().orElse(null), n.getContent());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        ClassOrInterfaceType scope = cloneNode(n.getScope(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        ClassOrInterfaceType r = new ClassOrInterfaceType(n.getTokenRange().orElse(null), scope, name, typeArguments, annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final PrimitiveType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        PrimitiveType r = new PrimitiveType(n.getTokenRange().orElse(null), n.getType(), annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        Type componentType = cloneNode(n.getComponentType(), arg);
        ArrayType r = new ArrayType(n.getTokenRange().orElse(null), componentType, n.getOrigin(), annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayCreationLevel n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression dimension = cloneNode(n.getDimension(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        ArrayCreationLevel r = new ArrayCreationLevel(n.getTokenRange().orElse(null), dimension, annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IntersectionType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        IntersectionType r = new IntersectionType(n.getTokenRange().orElse(null), elements);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnionType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        NodeList<ReferenceType> elements = cloneList(n.getElements(), arg);
        UnionType r = new UnionType(n.getTokenRange().orElse(null), elements);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VoidType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        VoidType r = new VoidType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final WildcardType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        ReferenceType superType = cloneNode(n.getSuperType(), arg);
        ReferenceType extendedType = cloneNode(n.getExtendedType(), arg);
        WildcardType r = new WildcardType(n.getTokenRange().orElse(null), extendedType, superType, annotations);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnknownType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        UnknownType r = new UnknownType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayAccessExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression name = cloneNode(n.getName(), arg);
        Expression index = cloneNode(n.getIndex(), arg);
        ArrayAccessExpr r = new ArrayAccessExpr(n.getTokenRange().orElse(null), name, index);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayCreationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<ArrayCreationLevel> levels = cloneList(n.getLevels(), arg);
        ArrayInitializerExpr initializer = cloneNode(n.getInitializer(), arg);
        Type elementType = cloneNode(n.getElementType(), arg);
        ArrayCreationExpr r = new ArrayCreationExpr(n.getTokenRange().orElse(null), elementType, levels, initializer);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ArrayInitializerExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Expression> values = cloneList(n.getValues(), arg);
        ArrayInitializerExpr r = new ArrayInitializerExpr(n.getTokenRange().orElse(null), values);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AssignExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        Expression target = cloneNode(n.getTarget(), arg);
        AssignExpr r = new AssignExpr(n.getTokenRange().orElse(null), target, value, n.getOperator());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BinaryExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression right = cloneNode(n.getRight(), arg);
        Expression left = cloneNode(n.getLeft(), arg);
        BinaryExpr r = new BinaryExpr(n.getTokenRange().orElse(null), left, right, n.getOperator());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CastExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Type type = cloneNode(n.getType(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        CastExpr r = new CastExpr(n.getTokenRange().orElse(null), type, expression);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ClassExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Type type = cloneNode(n.getType(), arg);
        ClassExpr r = new ClassExpr(n.getTokenRange().orElse(null), type);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ConditionalExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression thenExpr = cloneNode(n.getThenExpr(), arg);
        Expression elseExpr = cloneNode(n.getElseExpr(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        ConditionalExpr r = new ConditionalExpr(n.getTokenRange().orElse(null), condition, thenExpr, elseExpr);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EnclosedExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression inner = cloneNode(n.getInner(), arg);
        EnclosedExpr r = new EnclosedExpr(n.getTokenRange().orElse(null), inner);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final FieldAccessExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        FieldAccessExpr r = new FieldAccessExpr(n.getTokenRange().orElse(null), scope, typeArguments, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final InstanceOfExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        ReferenceType type = cloneNode(n.getType(), arg);
        PatternExpr pattern = cloneNode(n.getPattern(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        InstanceOfExpr r = new InstanceOfExpr(n.getTokenRange().orElse(null), expression, type, pattern);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final StringLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        StringLiteralExpr r = new StringLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IntegerLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        IntegerLiteralExpr r = new IntegerLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LongLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        LongLiteralExpr r = new LongLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CharLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        CharLiteralExpr r = new CharLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final DoubleLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        DoubleLiteralExpr r = new DoubleLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BooleanLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BooleanLiteralExpr r = new BooleanLiteralExpr(n.getTokenRange().orElse(null), n.isValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NullLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NullLiteralExpr r = new NullLiteralExpr(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodCallExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        MethodCallExpr r = new MethodCallExpr(n.getTokenRange().orElse(null), scope, typeArguments, name, arguments);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NameExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        NameExpr r = new NameExpr(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ObjectCreationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        ClassOrInterfaceType type = cloneNode(n.getType(), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        NodeList<BodyDeclaration<?>> anonymousClassBody = cloneList(n.getAnonymousClassBody().orElse(null), arg);
        ObjectCreationExpr r = new ObjectCreationExpr(n.getTokenRange().orElse(null), scope, type, typeArguments, arguments, anonymousClassBody);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Name n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name qualifier = cloneNode(n.getQualifier(), arg);
        Name r = new Name(n.getTokenRange().orElse(null), qualifier, n.getIdentifier());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SimpleName n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName r = new SimpleName(n.getTokenRange().orElse(null), n.getIdentifier());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ThisExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name typeName = cloneNode(n.getTypeName(), arg);
        ThisExpr r = new ThisExpr(n.getTokenRange().orElse(null), typeName);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SuperExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name typeName = cloneNode(n.getTypeName(), arg);
        SuperExpr r = new SuperExpr(n.getTokenRange().orElse(null), typeName);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnaryExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        UnaryExpr r = new UnaryExpr(n.getTokenRange().orElse(null), expression, n.getOperator());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VariableDeclarationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<VariableDeclarator> variables = cloneList(n.getVariables(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        VariableDeclarationExpr r = new VariableDeclarationExpr(n.getTokenRange().orElse(null), modifiers, annotations, variables);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MarkerAnnotationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        MarkerAnnotationExpr r = new MarkerAnnotationExpr(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SingleMemberAnnotationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        Expression memberValue = cloneNode(n.getMemberValue(), arg);
        SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(n.getTokenRange().orElse(null), name, memberValue);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final NormalAnnotationExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<MemberValuePair> pairs = cloneList(n.getPairs(), arg);
        NormalAnnotationExpr r = new NormalAnnotationExpr(n.getTokenRange().orElse(null), name, pairs);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MemberValuePair n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression value = cloneNode(n.getValue(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        MemberValuePair r = new MemberValuePair(n.getTokenRange().orElse(null), name, value);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ExplicitConstructorInvocationStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        NodeList<Expression> arguments = cloneList(n.getArguments(), arg);
        ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(n.getTokenRange().orElse(null), typeArguments, n.isThis(), expression, arguments);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LocalClassDeclarationStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        ClassOrInterfaceDeclaration classDeclaration = cloneNode(n.getClassDeclaration(), arg);
        LocalClassDeclarationStmt r = new LocalClassDeclarationStmt(n.getTokenRange().orElse(null), classDeclaration);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final AssertStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression message = cloneNode(n.getMessage(), arg);
        Expression check = cloneNode(n.getCheck(), arg);
        AssertStmt r = new AssertStmt(n.getTokenRange().orElse(null), check, message);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BlockStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        BlockStmt r = new BlockStmt(n.getTokenRange().orElse(null), statements);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LabeledStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Statement statement = cloneNode(n.getStatement(), arg);
        SimpleName label = cloneNode(n.getLabel(), arg);
        LabeledStmt r = new LabeledStmt(n.getTokenRange().orElse(null), label, statement);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final EmptyStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        EmptyStmt r = new EmptyStmt(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ExpressionStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        ExpressionStmt r = new ExpressionStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression selector = cloneNode(n.getSelector(), arg);
        NodeList<SwitchEntry> entries = cloneList(n.getEntries(), arg);
        SwitchStmt r = new SwitchStmt(n.getTokenRange().orElse(null), selector, entries);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchEntry n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Statement> statements = cloneList(n.getStatements(), arg);
        NodeList<Expression> labels = cloneList(n.getLabels(), arg);
        SwitchEntry r = new SwitchEntry(n.getTokenRange().orElse(null), labels, n.getType(), statements);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final BreakStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName label = cloneNode(n.getLabel(), arg);
        BreakStmt r = new BreakStmt(n.getTokenRange().orElse(null), label);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ReturnStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        ReturnStmt r = new ReturnStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final IfStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Statement thenStmt = cloneNode(n.getThenStmt(), arg);
        Statement elseStmt = cloneNode(n.getElseStmt(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        IfStmt r = new IfStmt(n.getTokenRange().orElse(null), condition, thenStmt, elseStmt);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final WhileStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Statement body = cloneNode(n.getBody(), arg);
        WhileStmt r = new WhileStmt(n.getTokenRange().orElse(null), condition, body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ContinueStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        SimpleName label = cloneNode(n.getLabel(), arg);
        ContinueStmt r = new ContinueStmt(n.getTokenRange().orElse(null), label);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final DoStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression condition = cloneNode(n.getCondition(), arg);
        Statement body = cloneNode(n.getBody(), arg);
        DoStmt r = new DoStmt(n.getTokenRange().orElse(null), body, condition);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ForEachStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        VariableDeclarationExpr variable = cloneNode(n.getVariable(), arg);
        Expression iterable = cloneNode(n.getIterable(), arg);
        Statement body = cloneNode(n.getBody(), arg);
        ForEachStmt r = new ForEachStmt(n.getTokenRange().orElse(null), variable, iterable, body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ForStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Expression> update = cloneList(n.getUpdate(), arg);
        NodeList<Expression> initialization = cloneList(n.getInitialization(), arg);
        Expression compare = cloneNode(n.getCompare(), arg);
        Statement body = cloneNode(n.getBody(), arg);
        ForStmt r = new ForStmt(n.getTokenRange().orElse(null), initialization, compare, update, body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ThrowStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        ThrowStmt r = new ThrowStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SynchronizedStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        BlockStmt body = cloneNode(n.getBody(), arg);
        SynchronizedStmt r = new SynchronizedStmt(n.getTokenRange().orElse(null), expression, body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TryStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        BlockStmt tryBlock = cloneNode(n.getTryBlock(), arg);
        NodeList<Expression> resources = cloneList(n.getResources(), arg);
        BlockStmt finallyBlock = cloneNode(n.getFinallyBlock(), arg);
        NodeList<CatchClause> catchClauses = cloneList(n.getCatchClauses(), arg);
        TryStmt r = new TryStmt(n.getTokenRange().orElse(null), resources, tryBlock, catchClauses, finallyBlock);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final CatchClause n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Parameter parameter = cloneNode(n.getParameter(), arg);
        BlockStmt body = cloneNode(n.getBody(), arg);
        CatchClause r = new CatchClause(n.getTokenRange().orElse(null), parameter, body);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final LambdaExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Parameter> parameters = cloneList(n.getParameters(), arg);
        Statement body = cloneNode(n.getBody(), arg);
        LambdaExpr r = new LambdaExpr(n.getTokenRange().orElse(null), parameters, body, n.isEnclosingParameters());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final MethodReferenceExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Type> typeArguments = cloneList(n.getTypeArguments().orElse(null), arg);
        Expression scope = cloneNode(n.getScope(), arg);
        MethodReferenceExpr r = new MethodReferenceExpr(n.getTokenRange().orElse(null), scope, typeArguments, n.getIdentifier());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TypeExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Type type = cloneNode(n.getType(), arg);
        TypeExpr r = new TypeExpr(n.getTokenRange().orElse(null), type);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
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
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        ImportDeclaration r = new ImportDeclaration(n.getTokenRange().orElse(null), name, n.isStatic(), n.isAsterisk());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleDeclaration n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<ModuleDirective> directives = cloneList(n.getDirectives(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        ModuleDeclaration r = new ModuleDeclaration(n.getTokenRange().orElse(null), annotations, name, n.isOpen(), directives);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleRequiresDirective n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<Modifier> modifiers = cloneList(n.getModifiers(), arg);
        ModuleRequiresDirective r = new ModuleRequiresDirective(n.getTokenRange().orElse(null), modifiers, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
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
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<Name> moduleNames = cloneList(n.getModuleNames(), arg);
        ModuleExportsDirective r = new ModuleExportsDirective(n.getTokenRange().orElse(null), name, moduleNames);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleProvidesDirective n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<Name> with = cloneList(n.getWith(), arg);
        Name name = cloneNode(n.getName(), arg);
        ModuleProvidesDirective r = new ModuleProvidesDirective(n.getTokenRange().orElse(null), name, with);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleUsesDirective n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        ModuleUsesDirective r = new ModuleUsesDirective(n.getTokenRange().orElse(null), name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ModuleOpensDirective n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<Name> moduleNames = cloneList(n.getModuleNames(), arg);
        ModuleOpensDirective r = new ModuleOpensDirective(n.getTokenRange().orElse(null), name, moduleNames);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final UnparsableStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        UnparsableStmt r = new UnparsableStmt(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final ReceiverParameter n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Type type = cloneNode(n.getType(), arg);
        Name name = cloneNode(n.getName(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        ReceiverParameter r = new ReceiverParameter(n.getTokenRange().orElse(null), annotations, type, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final VarType n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        NodeList<AnnotationExpr> annotations = cloneList(n.getAnnotations(), arg);
        VarType r = new VarType(n.getTokenRange().orElse(null));
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final Modifier n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Modifier r = new Modifier(n.getTokenRange().orElse(null), n.getKeyword());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final SwitchExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression selector = cloneNode(n.getSelector(), arg);
        NodeList<SwitchEntry> entries = cloneList(n.getEntries(), arg);
        SwitchExpr r = new SwitchExpr(n.getTokenRange().orElse(null), selector, entries);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    private void copyData(Node source, Node destination) {
        for (DataKey dataKey : source.getDataKeys()) {
            destination.setData(dataKey, source.getData(dataKey));
        }
    }

    @Override
    public Visitable visit(final YieldStmt n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        Expression expression = cloneNode(n.getExpression(), arg);
        YieldStmt r = new YieldStmt(n.getTokenRange().orElse(null), expression);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final TextBlockLiteralExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        TextBlockLiteralExpr r = new TextBlockLiteralExpr(n.getTokenRange().orElse(null), n.getValue());
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }

    @Override
    public Visitable visit(final PatternExpr n, final Object arg) {
        Comment comment = cloneNode(n.getComment(), arg);
        ReferenceType type = cloneNode(n.getType(), arg);
        SimpleName name = cloneNode(n.getName(), arg);
        PatternExpr r = new PatternExpr(n.getTokenRange().orElse(null), type, name);
        r.setComment(comment);
        n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);
        copyData(n, r);
        return r;
    }
}
