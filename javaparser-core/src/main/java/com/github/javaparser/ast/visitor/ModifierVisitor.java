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
import com.github.javaparser.utils.Pair;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.removeElementByObjectIdentity;
import static com.github.javaparser.utils.Utils.replaceElementByObjectIdentity;

/**
 * This visitor can be used to save time when some specific nodes needs
 * to be changed. To do that just extend this class and override the methods
 * from the nodes who needs to be changed, returning the changed node.
 * Returning null will remove the node.
 * <p>
 * If a node is removed that was required in its parent node,
 * the parent node will be removed too.
 *
 * @author Julio Vilmar Gesser
 */
public class ModifierVisitor<A> implements GenericVisitor<Visitable, A> {

    @Override
    public Visitable visit(final AnnotationDeclaration n, final A arg) {
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setMembers(members);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final AnnotationMemberDeclaration n, final A arg) {
        Expression defaultValue = n.getDefaultValue().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Type type = (Type) n.getType().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || type == null)
            return null;
        n.setDefaultValue(defaultValue);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setType(type);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ArrayAccessExpr n, final A arg) {
        Expression index = (Expression) n.getIndex().accept(this, arg);
        Expression name = (Expression) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (index == null || name == null)
            return null;
        n.setIndex(index);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ArrayCreationExpr n, final A arg) {
        Type elementType = (Type) n.getElementType().accept(this, arg);
        ArrayInitializerExpr initializer = n.getInitializer().map(s -> (ArrayInitializerExpr) s.accept(this, arg)).orElse(null);
        NodeList<ArrayCreationLevel> levels = modifyList(n.getLevels(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (elementType == null || levels.isEmpty())
            return null;
        n.setElementType(elementType);
        n.setInitializer(initializer);
        n.setLevels(levels);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ArrayInitializerExpr n, final A arg) {
        NodeList<Expression> values = modifyList(n.getValues(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setValues(values);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final AssertStmt n, final A arg) {
        Expression check = (Expression) n.getCheck().accept(this, arg);
        Expression message = n.getMessage().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (check == null)
            return null;
        n.setCheck(check);
        n.setMessage(message);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final AssignExpr n, final A arg) {
        Expression target = (Expression) n.getTarget().accept(this, arg);
        Expression value = (Expression) n.getValue().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (target == null || value == null)
            return null;
        n.setTarget(target);
        n.setValue(value);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final BinaryExpr n, final A arg) {
        Expression left = (Expression) n.getLeft().accept(this, arg);
        Expression right = (Expression) n.getRight().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (left == null)
            return right;
        if (right == null)
            return left;
        n.setLeft(left);
        n.setRight(right);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final BlockStmt n, final A arg) {
        NodeList<Statement> statements = modifyList(n.getStatements(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setStatements(statements);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final BooleanLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final BreakStmt n, final A arg) {
        Expression value = n.getValue().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setValue(value);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final CastExpr n, final A arg) {
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        Type type = (Type) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (expression == null || type == null)
            return null;
        n.setExpression(expression);
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final CatchClause n, final A arg) {
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        Parameter parameter = (Parameter) n.getParameter().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || parameter == null)
            return null;
        n.setBody(body);
        n.setParameter(parameter);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final CharLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ClassExpr n, final A arg) {
        Type type = (Type) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (type == null)
            return null;
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceDeclaration n, final A arg) {
        NodeList<ClassOrInterfaceType> extendedTypes = modifyList(n.getExtendedTypes(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = modifyList(n.getImplementedTypes(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setExtendedTypes(extendedTypes);
        n.setImplementedTypes(implementedTypes);
        n.setTypeParameters(typeParameters);
        n.setMembers(members);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceType n, final A arg) {
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        ClassOrInterfaceType scope = n.getScope().map(s -> (ClassOrInterfaceType) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setScope(scope);
        n.setTypeArguments(typeArguments);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final CompilationUnit n, final A arg) {
        NodeList<ImportDeclaration> imports = modifyList(n.getImports(), arg);
        ModuleDeclaration module = n.getModule().map(s -> (ModuleDeclaration) s.accept(this, arg)).orElse(null);
        PackageDeclaration packageDeclaration = n.getPackageDeclaration().map(s -> (PackageDeclaration) s.accept(this, arg)).orElse(null);
        NodeList<TypeDeclaration<?>> types = modifyList(n.getTypes(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setImports(imports);
        n.setModule(module);
        n.setPackageDeclaration(packageDeclaration);
        n.setTypes(types);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ConditionalExpr n, final A arg) {
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Expression elseExpr = (Expression) n.getElseExpr().accept(this, arg);
        Expression thenExpr = (Expression) n.getThenExpr().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (condition == null || elseExpr == null || thenExpr == null)
            return null;
        n.setCondition(condition);
        n.setElseExpr(elseExpr);
        n.setThenExpr(thenExpr);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ConstructorDeclaration n, final A arg) {
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        ReceiverParameter receiverParameter = n.getReceiverParameter().map(s -> (ReceiverParameter) s.accept(this, arg)).orElse(null);
        NodeList<ReferenceType> thrownExceptions = modifyList(n.getThrownExceptions(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || name == null)
            return null;
        n.setBody(body);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setParameters(parameters);
        n.setReceiverParameter(receiverParameter);
        n.setThrownExceptions(thrownExceptions);
        n.setTypeParameters(typeParameters);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ContinueStmt n, final A arg) {
        SimpleName label = n.getLabel().map(s -> (SimpleName) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setLabel(label);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final DoStmt n, final A arg) {
        Statement body = (Statement) n.getBody().accept(this, arg);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || condition == null)
            return null;
        n.setBody(body);
        n.setCondition(condition);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final DoubleLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final EmptyStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final EnclosedExpr n, final A arg) {
        Expression inner = (Expression) n.getInner().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (inner == null)
            return null;
        n.setInner(inner);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final EnumConstantDeclaration n, final A arg) {
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        NodeList<BodyDeclaration<?>> classBody = modifyList(n.getClassBody(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setArguments(arguments);
        n.setClassBody(classBody);
        n.setName(name);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final EnumDeclaration n, final A arg) {
        NodeList<EnumConstantDeclaration> entries = modifyList(n.getEntries(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = modifyList(n.getImplementedTypes(), arg);
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setEntries(entries);
        n.setImplementedTypes(implementedTypes);
        n.setMembers(members);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        Expression expression = n.getExpression().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setArguments(arguments);
        n.setExpression(expression);
        n.setTypeArguments(typeArguments);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ExpressionStmt n, final A arg) {
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (expression == null)
            return null;
        n.setExpression(expression);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final FieldAccessExpr n, final A arg) {
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Expression scope = (Expression) n.getScope().accept(this, arg);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || scope == null)
            return null;
        n.setName(name);
        n.setScope(scope);
        n.setTypeArguments(typeArguments);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final FieldDeclaration n, final A arg) {
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<VariableDeclarator> variables = modifyList(n.getVariables(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (variables.isEmpty())
            return null;
        n.setModifiers(modifiers);
        n.setVariables(variables);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ForEachStmt n, final A arg) {
        Statement body = (Statement) n.getBody().accept(this, arg);
        Expression iterable = (Expression) n.getIterable().accept(this, arg);
        VariableDeclarationExpr variable = (VariableDeclarationExpr) n.getVariable().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || iterable == null || variable == null)
            return null;
        n.setBody(body);
        n.setIterable(iterable);
        n.setVariable(variable);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ForStmt n, final A arg) {
        Statement body = (Statement) n.getBody().accept(this, arg);
        Expression compare = n.getCompare().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Expression> initialization = modifyList(n.getInitialization(), arg);
        NodeList<Expression> update = modifyList(n.getUpdate(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null)
            return null;
        n.setBody(body);
        n.setCompare(compare);
        n.setInitialization(initialization);
        n.setUpdate(update);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final IfStmt n, final A arg) {
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Statement elseStmt = n.getElseStmt().map(s -> (Statement) s.accept(this, arg)).orElse(null);
        Statement thenStmt = (Statement) n.getThenStmt().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (condition == null || thenStmt == null)
            return null;
        n.setCondition(condition);
        n.setElseStmt(elseStmt);
        n.setThenStmt(thenStmt);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final InitializerDeclaration n, final A arg) {
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null)
            return null;
        n.setBody(body);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final InstanceOfExpr n, final A arg) {
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        ReferenceType type = (ReferenceType) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (expression == null || type == null)
            return null;
        n.setExpression(expression);
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final IntegerLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final JavadocComment n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final LabeledStmt n, final A arg) {
        SimpleName label = (SimpleName) n.getLabel().accept(this, arg);
        Statement statement = (Statement) n.getStatement().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (label == null || statement == null)
            return null;
        n.setLabel(label);
        n.setStatement(statement);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final LongLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final MarkerAnnotationExpr n, final A arg) {
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final MemberValuePair n, final A arg) {
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Expression value = (Expression) n.getValue().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || value == null)
            return null;
        n.setName(name);
        n.setValue(value);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final MethodCallExpr n, final A arg) {
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Expression scope = n.getScope().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setArguments(arguments);
        n.setName(name);
        n.setScope(scope);
        n.setTypeArguments(typeArguments);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final MethodDeclaration n, final A arg) {
        BlockStmt body = n.getBody().map(s -> (BlockStmt) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        ReceiverParameter receiverParameter = n.getReceiverParameter().map(s -> (ReceiverParameter) s.accept(this, arg)).orElse(null);
        NodeList<ReferenceType> thrownExceptions = modifyList(n.getThrownExceptions(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (type == null || name == null)
            return null;
        n.setBody(body);
        n.setType(type);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setParameters(parameters);
        n.setReceiverParameter(receiverParameter);
        n.setThrownExceptions(thrownExceptions);
        n.setTypeParameters(typeParameters);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final NameExpr n, final A arg) {
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final NormalAnnotationExpr n, final A arg) {
        NodeList<MemberValuePair> pairs = modifyList(n.getPairs(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setPairs(pairs);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final NullLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ObjectCreationExpr n, final A arg) {
        NodeList<BodyDeclaration<?>> anonymousClassBody = modifyList(n.getAnonymousClassBody(), arg);
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        Expression scope = n.getScope().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        ClassOrInterfaceType type = (ClassOrInterfaceType) n.getType().accept(this, arg);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (type == null)
            return null;
        n.setAnonymousClassBody(anonymousClassBody);
        n.setArguments(arguments);
        n.setScope(scope);
        n.setType(type);
        n.setTypeArguments(typeArguments);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final PackageDeclaration n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setAnnotations(annotations);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final Parameter n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Type type = (Type) n.getType().accept(this, arg);
        NodeList<AnnotationExpr> varArgsAnnotations = modifyList(n.getVarArgsAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || type == null)
            return null;
        n.setAnnotations(annotations);
        n.setModifiers(modifiers);
        n.setName(name);
        n.setType(type);
        n.setVarArgsAnnotations(varArgsAnnotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final Name n, final A arg) {
        Name qualifier = n.getQualifier().map(s -> (Name) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setQualifier(qualifier);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final PrimitiveType n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SimpleName n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ArrayType n, final A arg) {
        Type componentType = (Type) n.getComponentType().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (componentType == null)
            return null;
        n.setComponentType(componentType);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ArrayCreationLevel n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Expression dimension = n.getDimension().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setAnnotations(annotations);
        n.setDimension(dimension);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final IntersectionType n, final A arg) {
        NodeList<ReferenceType> elements = modifyList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (elements.isEmpty())
            return null;
        n.setElements(elements);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final UnionType n, final A arg) {
        NodeList<ReferenceType> elements = modifyList(n.getElements(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (elements.isEmpty())
            return null;
        n.setElements(elements);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ReturnStmt n, final A arg) {
        Expression expression = n.getExpression().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setExpression(expression);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SingleMemberAnnotationExpr n, final A arg) {
        Expression memberValue = (Expression) n.getMemberValue().accept(this, arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (memberValue == null || name == null)
            return null;
        n.setMemberValue(memberValue);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final StringLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SuperExpr n, final A arg) {
        Name typeName = n.getTypeName().map(s -> (Name) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setTypeName(typeName);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SwitchEntry n, final A arg) {
        NodeList<Expression> labels = modifyList(n.getLabels(), arg);
        NodeList<Statement> statements = modifyList(n.getStatements(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setLabels(labels);
        n.setStatements(statements);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SwitchStmt n, final A arg) {
        NodeList<SwitchEntry> entries = modifyList(n.getEntries(), arg);
        Expression selector = (Expression) n.getSelector().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (selector == null)
            return null;
        n.setEntries(entries);
        n.setSelector(selector);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SynchronizedStmt n, final A arg) {
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || expression == null)
            return null;
        n.setBody(body);
        n.setExpression(expression);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ThisExpr n, final A arg) {
        Name typeName = n.getTypeName().map(s -> (Name) s.accept(this, arg)).orElse(null);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setTypeName(typeName);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ThrowStmt n, final A arg) {
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (expression == null)
            return null;
        n.setExpression(expression);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final TryStmt n, final A arg) {
        NodeList<CatchClause> catchClauses = modifyList(n.getCatchClauses(), arg);
        BlockStmt finallyBlock = n.getFinallyBlock().map(s -> (BlockStmt) s.accept(this, arg)).orElse(null);
        NodeList<Expression> resources = modifyList(n.getResources(), arg);
        BlockStmt tryBlock = (BlockStmt) n.getTryBlock().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (tryBlock == null)
            return null;
        n.setCatchClauses(catchClauses);
        n.setFinallyBlock(finallyBlock);
        n.setResources(resources);
        n.setTryBlock(tryBlock);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final LocalClassDeclarationStmt n, final A arg) {
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) n.getClassDeclaration().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (classDeclaration == null)
            return null;
        n.setClassDeclaration(classDeclaration);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final TypeParameter n, final A arg) {
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<ClassOrInterfaceType> typeBound = modifyList(n.getTypeBound(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setTypeBound(typeBound);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final UnaryExpr n, final A arg) {
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (expression == null)
            return null;
        n.setExpression(expression);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final UnknownType n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final VariableDeclarationExpr n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<VariableDeclarator> variables = modifyList(n.getVariables(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (variables.isEmpty())
            return null;
        n.setAnnotations(annotations);
        n.setModifiers(modifiers);
        n.setVariables(variables);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final VariableDeclarator n, final A arg) {
        Expression initializer = n.getInitializer().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Type type = (Type) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || type == null)
            return null;
        n.setInitializer(initializer);
        n.setName(name);
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final VoidType n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final WhileStmt n, final A arg) {
        Statement body = (Statement) n.getBody().accept(this, arg);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null || condition == null)
            return null;
        n.setBody(body);
        n.setCondition(condition);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final WildcardType n, final A arg) {
        ReferenceType extendedType = n.getExtendedType().map(s -> (ReferenceType) s.accept(this, arg)).orElse(null);
        ReferenceType superType = n.getSuperType().map(s -> (ReferenceType) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setExtendedType(extendedType);
        n.setSuperType(superType);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final LambdaExpr n, final A arg) {
        Statement body = (Statement) n.getBody().accept(this, arg);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (body == null)
            return null;
        n.setBody(body);
        n.setParameters(parameters);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final MethodReferenceExpr n, final A arg) {
        Expression scope = (Expression) n.getScope().accept(this, arg);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (scope == null)
            return null;
        n.setScope(scope);
        n.setTypeArguments(typeArguments);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final TypeExpr n, final A arg) {
        Type type = (Type) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (type == null)
            return null;
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(NodeList n, A arg) {
        if (n.isEmpty()) {
            return n;
        }
        final List<Pair<Node, Node>> changeList = new ArrayList<>();
        final List<Node> listCopy = new ArrayList<>(n);
        for (Node node : listCopy) {
            final Node newNode = (Node) node.accept(this, arg);
            changeList.add(new Pair<>(node, newNode));
        }
        for (Pair<Node, Node> change : changeList) {
            if (change.b == null) {
                removeElementByObjectIdentity(n, change.a);
            } else {
                replaceElementByObjectIdentity(n, change.a, change.b);
            }
        }
        return n;
    }

    @Override
    public Node visit(final ImportDeclaration n, final A arg) {
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final BlockComment n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final LineComment n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    private <N extends Node> NodeList<N> modifyList(NodeList<N> list, A arg) {
        return (NodeList<N>) list.accept(this, arg);
    }

    private <N extends Node> NodeList<N> modifyList(Optional<NodeList<N>> list, A arg) {
        return list.map(ns -> modifyList(ns, arg)).orElse(null);
    }

    public Visitable visit(final ModuleDeclaration n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<ModuleDirective> directives = modifyList(n.getDirectives(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setAnnotations(annotations);
        n.setDirectives(directives);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    public Visitable visit(final ModuleRequiresDirective n, final A arg) {
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setModifiers(modifiers);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleExportsDirective n, final A arg) {
        NodeList<Name> moduleNames = modifyList(n.getModuleNames(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setModuleNames(moduleNames);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleProvidesDirective n, final A arg) {
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<Name> with = modifyList(n.getWith(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setWith(with);
        n.setComment(comment);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleUsesDirective n, final A arg) {
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ModuleOpensDirective n, final A arg) {
        NodeList<Name> moduleNames = modifyList(n.getModuleNames(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null)
            return null;
        n.setModuleNames(moduleNames);
        n.setName(name);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final UnparsableStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final ReceiverParameter n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        Type type = (Type) n.getType().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (name == null || type == null)
            return null;
        n.setAnnotations(annotations);
        n.setName(name);
        n.setType(type);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final VarType n, final A arg) {
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setAnnotations(annotations);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final Modifier n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final SwitchExpr n, final A arg) {
        NodeList<SwitchEntry> entries = modifyList(n.getEntries(), arg);
        Expression selector = (Expression) n.getSelector().accept(this, arg);
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        if (selector == null)
            return null;
        n.setEntries(entries);
        n.setSelector(selector);
        n.setComment(comment);
        return n;
    }
}
