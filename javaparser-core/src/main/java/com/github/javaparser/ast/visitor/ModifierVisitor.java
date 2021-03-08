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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setMembers(members);
        return n;
    }

    @Override
    public Visitable visit(final AnnotationMemberDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Type type = (Type) n.getType().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        Expression defaultValue = n.getDefaultValue().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        if (type == null || name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setType(type);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setDefaultValue(defaultValue);
        return n;
    }

    @Override
    public Visitable visit(final ArrayAccessExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression name = (Expression) n.getName().accept(this, arg);
        Expression index = (Expression) n.getIndex().accept(this, arg);
        if (name == null || index == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setIndex(index);
        return n;
    }

    @Override
    public Visitable visit(final ArrayCreationExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<ArrayCreationLevel> levels = modifyList(n.getLevels(), arg);
        ArrayInitializerExpr initializer = n.getInitializer().map(s -> (ArrayInitializerExpr) s.accept(this, arg)).orElse(null);
        Type elementType = (Type) n.getElementType().accept(this, arg);
        if (levels.isEmpty() || elementType == null)
            return null;
        n.setComment(comment);
        n.setLevels(levels);
        n.setInitializer(initializer);
        n.setElementType(elementType);
        return n;
    }

    @Override
    public Visitable visit(final ArrayInitializerExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Expression> values = modifyList(n.getValues(), arg);
        n.setComment(comment);
        n.setValues(values);
        return n;
    }

    @Override
    public Visitable visit(final AssertStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression message = n.getMessage().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Expression check = (Expression) n.getCheck().accept(this, arg);
        if (check == null)
            return null;
        n.setComment(comment);
        n.setMessage(message);
        n.setCheck(check);
        return n;
    }

    @Override
    public Visitable visit(final AssignExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression value = (Expression) n.getValue().accept(this, arg);
        Expression target = (Expression) n.getTarget().accept(this, arg);
        if (value == null || target == null)
            return null;
        n.setComment(comment);
        n.setValue(value);
        n.setTarget(target);
        return n;
    }

    @Override
    public Visitable visit(final BinaryExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression right = (Expression) n.getRight().accept(this, arg);
        Expression left = (Expression) n.getLeft().accept(this, arg);
        if (left == null)
            return right;
        if (right == null)
            return left;
        n.setComment(comment);
        n.setRight(right);
        n.setLeft(left);
        return n;
    }

    @Override
    public Visitable visit(final BlockStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Statement> statements = modifyList(n.getStatements(), arg);
        n.setComment(comment);
        n.setStatements(statements);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        SimpleName label = n.getLabel().map(s -> (SimpleName) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setLabel(label);
        return n;
    }

    @Override
    public Visitable visit(final CastExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (type == null || expression == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final CatchClause n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Parameter parameter = (Parameter) n.getParameter().accept(this, arg);
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        if (parameter == null || body == null)
            return null;
        n.setComment(comment);
        n.setParameter(parameter);
        n.setBody(body);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        if (type == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        return n;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = modifyList(n.getImplementedTypes(), arg);
        NodeList<ClassOrInterfaceType> extendedTypes = modifyList(n.getExtendedTypes(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setMembers(members);
        n.setTypeParameters(typeParameters);
        n.setImplementedTypes(implementedTypes);
        n.setExtendedTypes(extendedTypes);
        return n;
    }

    @Override
    public Visitable visit(final ClassOrInterfaceType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        ClassOrInterfaceType scope = n.getScope().map(s -> (ClassOrInterfaceType) s.accept(this, arg)).orElse(null);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setTypeArguments(typeArguments);
        n.setScope(scope);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final CompilationUnit n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<TypeDeclaration<?>> types = modifyList(n.getTypes(), arg);
        PackageDeclaration packageDeclaration = n.getPackageDeclaration().map(s -> (PackageDeclaration) s.accept(this, arg)).orElse(null);
        ModuleDeclaration module = n.getModule().map(s -> (ModuleDeclaration) s.accept(this, arg)).orElse(null);
        NodeList<ImportDeclaration> imports = modifyList(n.getImports(), arg);
        n.setComment(comment);
        n.setTypes(types);
        n.setPackageDeclaration(packageDeclaration);
        n.setModule(module);
        n.setImports(imports);
        return n;
    }

    @Override
    public Visitable visit(final ConditionalExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression thenExpr = (Expression) n.getThenExpr().accept(this, arg);
        Expression elseExpr = (Expression) n.getElseExpr().accept(this, arg);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        if (thenExpr == null || elseExpr == null || condition == null)
            return null;
        n.setComment(comment);
        n.setThenExpr(thenExpr);
        n.setElseExpr(elseExpr);
        n.setCondition(condition);
        return n;
    }

    @Override
    public Visitable visit(final ConstructorDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = modifyList(n.getThrownExceptions(), arg);
        ReceiverParameter receiverParameter = n.getReceiverParameter().map(s -> (ReceiverParameter) s.accept(this, arg)).orElse(null);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        if (name == null || body == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setTypeParameters(typeParameters);
        n.setThrownExceptions(thrownExceptions);
        n.setReceiverParameter(receiverParameter);
        n.setParameters(parameters);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final ContinueStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        SimpleName label = n.getLabel().map(s -> (SimpleName) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setLabel(label);
        return n;
    }

    @Override
    public Visitable visit(final DoStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Statement body = (Statement) n.getBody().accept(this, arg);
        if (condition == null || body == null)
            return null;
        n.setComment(comment);
        n.setCondition(condition);
        n.setBody(body);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression inner = (Expression) n.getInner().accept(this, arg);
        if (inner == null)
            return null;
        n.setComment(comment);
        n.setInner(inner);
        return n;
    }

    @Override
    public Visitable visit(final EnumConstantDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<BodyDeclaration<?>> classBody = modifyList(n.getClassBody(), arg);
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setName(name);
        n.setClassBody(classBody);
        n.setArguments(arguments);
        return n;
    }

    @Override
    public Visitable visit(final EnumDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<BodyDeclaration<?>> members = modifyList(n.getMembers(), arg);
        NodeList<ClassOrInterfaceType> implementedTypes = modifyList(n.getImplementedTypes(), arg);
        NodeList<EnumConstantDeclaration> entries = modifyList(n.getEntries(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setMembers(members);
        n.setImplementedTypes(implementedTypes);
        n.setEntries(entries);
        return n;
    }

    @Override
    public Visitable visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Expression expression = n.getExpression().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        n.setComment(comment);
        n.setTypeArguments(typeArguments);
        n.setExpression(expression);
        n.setArguments(arguments);
        return n;
    }

    @Override
    public Visitable visit(final ExpressionStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (expression == null)
            return null;
        n.setComment(comment);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final FieldAccessExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Expression scope = (Expression) n.getScope().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (scope == null || name == null)
            return null;
        n.setComment(comment);
        n.setTypeArguments(typeArguments);
        n.setScope(scope);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final FieldDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<VariableDeclarator> variables = modifyList(n.getVariables(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        if (variables.isEmpty())
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setVariables(variables);
        n.setModifiers(modifiers);
        return n;
    }

    @Override
    public Visitable visit(final ForEachStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        VariableDeclarationExpr variable = (VariableDeclarationExpr) n.getVariable().accept(this, arg);
        Expression iterable = (Expression) n.getIterable().accept(this, arg);
        Statement body = (Statement) n.getBody().accept(this, arg);
        if (variable == null || iterable == null || body == null)
            return null;
        n.setComment(comment);
        n.setVariable(variable);
        n.setIterable(iterable);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final ForStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Expression> update = modifyList(n.getUpdate(), arg);
        NodeList<Expression> initialization = modifyList(n.getInitialization(), arg);
        Expression compare = n.getCompare().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        Statement body = (Statement) n.getBody().accept(this, arg);
        if (body == null)
            return null;
        n.setComment(comment);
        n.setUpdate(update);
        n.setInitialization(initialization);
        n.setCompare(compare);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final IfStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Statement thenStmt = (Statement) n.getThenStmt().accept(this, arg);
        Statement elseStmt = n.getElseStmt().map(s -> (Statement) s.accept(this, arg)).orElse(null);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        if (thenStmt == null || condition == null)
            return null;
        n.setComment(comment);
        n.setThenStmt(thenStmt);
        n.setElseStmt(elseStmt);
        n.setCondition(condition);
        return n;
    }

    @Override
    public Visitable visit(final InitializerDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        if (body == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final InstanceOfExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        ReferenceType type = (ReferenceType) n.getType().accept(this, arg);
        PatternExpr pattern = n.getPattern().map(s -> (PatternExpr) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (type == null || expression == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        n.setPattern(pattern);
        n.setExpression(expression);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Statement statement = (Statement) n.getStatement().accept(this, arg);
        SimpleName label = (SimpleName) n.getLabel().accept(this, arg);
        if (statement == null || label == null)
            return null;
        n.setComment(comment);
        n.setStatement(statement);
        n.setLabel(label);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final MemberValuePair n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression value = (Expression) n.getValue().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (value == null || name == null)
            return null;
        n.setComment(comment);
        n.setValue(value);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final MethodCallExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Expression scope = n.getScope().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setTypeArguments(typeArguments);
        n.setScope(scope);
        n.setName(name);
        n.setArguments(arguments);
        return n;
    }

    @Override
    public Visitable visit(final MethodDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<TypeParameter> typeParameters = modifyList(n.getTypeParameters(), arg);
        NodeList<ReferenceType> thrownExceptions = modifyList(n.getThrownExceptions(), arg);
        ReceiverParameter receiverParameter = n.getReceiverParameter().map(s -> (ReceiverParameter) s.accept(this, arg)).orElse(null);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        Type type = (Type) n.getType().accept(this, arg);
        BlockStmt body = n.getBody().map(s -> (BlockStmt) s.accept(this, arg)).orElse(null);
        if (name == null || type == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setTypeParameters(typeParameters);
        n.setThrownExceptions(thrownExceptions);
        n.setReceiverParameter(receiverParameter);
        n.setParameters(parameters);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setType(type);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final NameExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final NormalAnnotationExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<MemberValuePair> pairs = modifyList(n.getPairs(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setPairs(pairs);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        ClassOrInterfaceType type = (ClassOrInterfaceType) n.getType().accept(this, arg);
        Expression scope = n.getScope().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<Expression> arguments = modifyList(n.getArguments(), arg);
        NodeList<BodyDeclaration<?>> anonymousClassBody = modifyList(n.getAnonymousClassBody(), arg);
        if (type == null)
            return null;
        n.setComment(comment);
        n.setTypeArguments(typeArguments);
        n.setType(type);
        n.setScope(scope);
        n.setArguments(arguments);
        n.setAnonymousClassBody(anonymousClassBody);
        return n;
    }

    @Override
    public Visitable visit(final PackageDeclaration n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final Parameter n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> varArgsAnnotations = modifyList(n.getVarArgsAnnotations(), arg);
        Type type = (Type) n.getType().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        if (type == null || name == null)
            return null;
        n.setComment(comment);
        n.setVarArgsAnnotations(varArgsAnnotations);
        n.setType(type);
        n.setName(name);
        n.setModifiers(modifiers);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final Name n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name qualifier = n.getQualifier().map(s -> (Name) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setQualifier(qualifier);
        return n;
    }

    @Override
    public Visitable visit(final PrimitiveType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        n.setComment(comment);
        n.setAnnotations(annotations);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        Type componentType = (Type) n.getComponentType().accept(this, arg);
        if (componentType == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setComponentType(componentType);
        return n;
    }

    @Override
    public Visitable visit(final ArrayCreationLevel n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression dimension = n.getDimension().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        n.setComment(comment);
        n.setDimension(dimension);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final IntersectionType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<ReferenceType> elements = modifyList(n.getElements(), arg);
        if (elements.isEmpty())
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setElements(elements);
        return n;
    }

    @Override
    public Visitable visit(final UnionType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<ReferenceType> elements = modifyList(n.getElements(), arg);
        if (elements.isEmpty())
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setElements(elements);
        return n;
    }

    @Override
    public Visitable visit(final ReturnStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = n.getExpression().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final SingleMemberAnnotationExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        Expression memberValue = (Expression) n.getMemberValue().accept(this, arg);
        if (name == null || memberValue == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setMemberValue(memberValue);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name typeName = n.getTypeName().map(s -> (Name) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setTypeName(typeName);
        return n;
    }

    @Override
    public Visitable visit(final SwitchEntry n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Statement> statements = modifyList(n.getStatements(), arg);
        NodeList<Expression> labels = modifyList(n.getLabels(), arg);
        n.setComment(comment);
        n.setStatements(statements);
        n.setLabels(labels);
        return n;
    }

    @Override
    public Visitable visit(final SwitchStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression selector = (Expression) n.getSelector().accept(this, arg);
        NodeList<SwitchEntry> entries = modifyList(n.getEntries(), arg);
        if (selector == null)
            return null;
        n.setComment(comment);
        n.setSelector(selector);
        n.setEntries(entries);
        return n;
    }

    @Override
    public Visitable visit(final SynchronizedStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        BlockStmt body = (BlockStmt) n.getBody().accept(this, arg);
        if (expression == null || body == null)
            return null;
        n.setComment(comment);
        n.setExpression(expression);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final ThisExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name typeName = n.getTypeName().map(s -> (Name) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setTypeName(typeName);
        return n;
    }

    @Override
    public Visitable visit(final ThrowStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (expression == null)
            return null;
        n.setComment(comment);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final TryStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        BlockStmt tryBlock = (BlockStmt) n.getTryBlock().accept(this, arg);
        NodeList<Expression> resources = modifyList(n.getResources(), arg);
        BlockStmt finallyBlock = n.getFinallyBlock().map(s -> (BlockStmt) s.accept(this, arg)).orElse(null);
        NodeList<CatchClause> catchClauses = modifyList(n.getCatchClauses(), arg);
        if (tryBlock == null)
            return null;
        n.setComment(comment);
        n.setTryBlock(tryBlock);
        n.setResources(resources);
        n.setFinallyBlock(finallyBlock);
        n.setCatchClauses(catchClauses);
        return n;
    }

    @Override
    public Visitable visit(final LocalClassDeclarationStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) n.getClassDeclaration().accept(this, arg);
        if (classDeclaration == null)
            return null;
        n.setComment(comment);
        n.setClassDeclaration(classDeclaration);
        return n;
    }

    @Override
    public Visitable visit(final TypeParameter n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        NodeList<ClassOrInterfaceType> typeBound = modifyList(n.getTypeBound(), arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setTypeBound(typeBound);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final UnaryExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (expression == null)
            return null;
        n.setComment(comment);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final UnknownType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        n.setComment(comment);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final VariableDeclarationExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<VariableDeclarator> variables = modifyList(n.getVariables(), arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        if (variables.isEmpty())
            return null;
        n.setComment(comment);
        n.setVariables(variables);
        n.setModifiers(modifiers);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final VariableDeclarator n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        Expression initializer = n.getInitializer().map(s -> (Expression) s.accept(this, arg)).orElse(null);
        if (type == null || name == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        n.setName(name);
        n.setInitializer(initializer);
        return n;
    }

    @Override
    public Visitable visit(final VoidType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        n.setComment(comment);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final WhileStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression condition = (Expression) n.getCondition().accept(this, arg);
        Statement body = (Statement) n.getBody().accept(this, arg);
        if (condition == null || body == null)
            return null;
        n.setComment(comment);
        n.setCondition(condition);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final WildcardType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        ReferenceType superType = n.getSuperType().map(s -> (ReferenceType) s.accept(this, arg)).orElse(null);
        ReferenceType extendedType = n.getExtendedType().map(s -> (ReferenceType) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        n.setAnnotations(annotations);
        n.setSuperType(superType);
        n.setExtendedType(extendedType);
        return n;
    }

    @Override
    public Visitable visit(final LambdaExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Parameter> parameters = modifyList(n.getParameters(), arg);
        Statement body = (Statement) n.getBody().accept(this, arg);
        if (body == null)
            return null;
        n.setComment(comment);
        n.setParameters(parameters);
        n.setBody(body);
        return n;
    }

    @Override
    public Visitable visit(final MethodReferenceExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Type> typeArguments = modifyList(n.getTypeArguments(), arg);
        Expression scope = (Expression) n.getScope().accept(this, arg);
        if (scope == null)
            return null;
        n.setComment(comment);
        n.setTypeArguments(typeArguments);
        n.setScope(scope);
        return n;
    }

    @Override
    public Visitable visit(final TypeExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        if (type == null)
            return null;
        n.setComment(comment);
        n.setType(type);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<ModuleDirective> directives = modifyList(n.getDirectives(), arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setDirectives(directives);
        n.setAnnotations(annotations);
        return n;
    }

    public Visitable visit(final ModuleRequiresDirective n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<Modifier> modifiers = modifyList(n.getModifiers(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setModifiers(modifiers);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleExportsDirective n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<Name> moduleNames = modifyList(n.getModuleNames(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setModuleNames(moduleNames);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleProvidesDirective n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<Name> with = modifyList(n.getWith(), arg);
        Name name = (Name) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setWith(with);
        n.setName(name);
        return n;
    }

    @Override()
    public Visitable visit(final ModuleUsesDirective n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        return n;
    }

    @Override
    public Visitable visit(final ModuleOpensDirective n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<Name> moduleNames = modifyList(n.getModuleNames(), arg);
        if (name == null)
            return null;
        n.setComment(comment);
        n.setName(name);
        n.setModuleNames(moduleNames);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Type type = (Type) n.getType().accept(this, arg);
        Name name = (Name) n.getName().accept(this, arg);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        if (type == null || name == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        n.setName(name);
        n.setAnnotations(annotations);
        return n;
    }

    @Override
    public Visitable visit(final VarType n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        NodeList<AnnotationExpr> annotations = modifyList(n.getAnnotations(), arg);
        n.setComment(comment);
        n.setAnnotations(annotations);
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
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression selector = (Expression) n.getSelector().accept(this, arg);
        NodeList<SwitchEntry> entries = modifyList(n.getEntries(), arg);
        if (selector == null)
            return null;
        n.setComment(comment);
        n.setSelector(selector);
        n.setEntries(entries);
        return n;
    }

    @Override
    public Visitable visit(final YieldStmt n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        Expression expression = (Expression) n.getExpression().accept(this, arg);
        if (expression == null)
            return null;
        n.setComment(comment);
        n.setExpression(expression);
        return n;
    }

    @Override
    public Visitable visit(final TextBlockLiteralExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        n.setComment(comment);
        return n;
    }

    @Override
    public Visitable visit(final PatternExpr n, final A arg) {
        Comment comment = n.getComment().map(s -> (Comment) s.accept(this, arg)).orElse(null);
        ReferenceType type = (ReferenceType) n.getType().accept(this, arg);
        SimpleName name = (SimpleName) n.getName().accept(this, arg);
        if (type == null || name == null)
            return null;
        n.setComment(comment);
        n.setType(type);
        n.setName(name);
        return n;
    }
}
