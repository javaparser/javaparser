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
package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.EnumSet;

class Context {
    public final String name;
    public final int indent;

    public Context(String name, int indent) {
        this.name = name;
        this.indent = indent;
    }

    public Context() {
        this("root", 0);
    }
}

/**
 * A visitor that creates a simple visualisation of the AST.
 */
public class TreeStructureVisitor extends VoidVisitorAdapter<Context> {

    private final Callback callback;

    public interface Callback {

        void exitNode(Node n, String name, Integer indent);

        void enterNode(Node n, String name, Integer indent);

        void outputProperty(Node node, String name, EnumSet<Modifier> modifiers, Integer indent);

        void outputProperty(Node node, String name, Enum<?> e, Integer indent);

        void outputProperty(Node node, String name, String content, Integer indent);

        void outputProperty(Node node, String name, boolean value, Integer indent);
    }

    public TreeStructureVisitor(Callback callback) {
        this.callback = callback;
    }

    @Override
    public void visit(NodeList n, Context arg) {
        ((NodeList<Node>) n).forEach(x -> x.accept(this, arg));
    }

    public void visit(AnnotationDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getMembers().accept(this, new Context("members", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(AnnotationMemberDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getDefaultValue().ifPresent(c -> c.accept(this, new Context("defaultValue", arg.indent + 1)));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ArrayAccessExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getIndex().accept(this, new Context("index", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ArrayCreationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getElementType().accept(this, new Context("elementType", arg.indent + 1));
        n.getInitializer().ifPresent(c -> c.accept(this, new Context("initializer", arg.indent + 1)));
        n.getLevels().accept(this, new Context("levels", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ArrayCreationLevel n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getDimension().ifPresent(c -> c.accept(this, new Context("dimension", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ArrayInitializerExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getValues().accept(this, new Context("values", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ArrayType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getComponentType().accept(this, new Context("componentType", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(AssertStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getCheck().accept(this, new Context("check", arg.indent + 1));
        n.getMessage().ifPresent(c -> c.accept(this, new Context("message", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(AssignExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "operator", n.getOperator(), arg.indent + 1);
        n.getTarget().accept(this, new Context("target", arg.indent + 1));
        n.getValue().accept(this, new Context("value", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(BinaryExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "operator", n.getOperator(), arg.indent + 1);
        n.getLeft().accept(this, new Context("left", arg.indent + 1));
        n.getRight().accept(this, new Context("right", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(BlockComment n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "content", n.getContent(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(BlockStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getStatements().accept(this, new Context("statements", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(BooleanLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(BreakStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getLabel().ifPresent(c -> c.accept(this, new Context("label", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(CastExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(CatchClause n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getParameter().accept(this, new Context("parameter", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(CharLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ClassExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ClassOrInterfaceDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isInterface", n.isInterface(), arg.indent + 1);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getExtendedTypes().accept(this, new Context("extendedTypes", arg.indent + 1));
        n.getImplementedTypes().accept(this, new Context("implementedTypes", arg.indent + 1));
        n.getTypeParameters().accept(this, new Context("typeParameters", arg.indent + 1));
        n.getMembers().accept(this, new Context("members", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ClassOrInterfaceType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getScope().ifPresent(c -> c.accept(this, new Context("scope", arg.indent + 1)));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(CompilationUnit n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getImports().accept(this, new Context("imports", arg.indent + 1));
        n.getPackageDeclaration().ifPresent(c -> c.accept(this, new Context("packageDeclaration", arg.indent + 1)));
        n.getTypes().accept(this, new Context("types", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ConditionalExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getCondition().accept(this, new Context("condition", arg.indent + 1));
        n.getElseExpr().accept(this, new Context("elseExpr", arg.indent + 1));
        n.getThenExpr().accept(this, new Context("thenExpr", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ConstructorDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getParameters().accept(this, new Context("parameters", arg.indent + 1));
        n.getThrownExceptions().accept(this, new Context("thrownExceptions", arg.indent + 1));
        n.getTypeParameters().accept(this, new Context("typeParameters", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ContinueStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getLabel().ifPresent(c -> c.accept(this, new Context("label", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(DoStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getCondition().accept(this, new Context("condition", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(DoubleLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(EmptyMemberDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(EmptyStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(EnclosedExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getInner().ifPresent(c -> c.accept(this, new Context("inner", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(EnumConstantDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getArguments().accept(this, new Context("arguments", arg.indent + 1));
        n.getClassBody().accept(this, new Context("classBody", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(EnumDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getEntries().accept(this, new Context("entries", arg.indent + 1));
        n.getImplementedTypes().accept(this, new Context("implementedTypes", arg.indent + 1));
        n.getMembers().accept(this, new Context("members", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ExplicitConstructorInvocationStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isThis", n.isThis(), arg.indent + 1);
        n.getArguments().accept(this, new Context("arguments", arg.indent + 1));
        n.getExpression().ifPresent(c -> c.accept(this, new Context("expression", arg.indent + 1)));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ExpressionStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(FieldAccessExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getScope().ifPresent(c -> c.accept(this, new Context("scope", arg.indent + 1)));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(FieldDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getVariables().accept(this, new Context("variables", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ForStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getCompare().ifPresent(c -> c.accept(this, new Context("compare", arg.indent + 1)));
        n.getInitialization().accept(this, new Context("initialization", arg.indent + 1));
        n.getUpdate().accept(this, new Context("update", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ForeachStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getIterable().accept(this, new Context("iterable", arg.indent + 1));
        n.getVariable().accept(this, new Context("variable", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(IfStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getCondition().accept(this, new Context("condition", arg.indent + 1));
        n.getElseStmt().ifPresent(c -> c.accept(this, new Context("elseStmt", arg.indent + 1)));
        n.getThenStmt().accept(this, new Context("thenStmt", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ImportDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isAsterisk", n.isAsterisk(), arg.indent + 1);
        callback.outputProperty(n, "isStatic", n.isStatic(), arg.indent + 1);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(InitializerDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isStatic", n.isStatic(), arg.indent + 1);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(InstanceOfExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(IntegerLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(IntersectionType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getElements().accept(this, new Context("elements", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(JavadocComment n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "content", n.getContent(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(LabeledStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getLabel().accept(this, new Context("label", arg.indent + 1));
        n.getStatement().accept(this, new Context("statement", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(LambdaExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isEnclosingParameters", n.isEnclosingParameters(), arg.indent + 1);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getParameters().accept(this, new Context("parameters", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(LineComment n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "content", n.getContent(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(LocalClassDeclarationStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getClassDeclaration().accept(this, new Context("classDeclaration", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(LongLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(MarkerAnnotationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(MemberValuePair n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getValue().accept(this, new Context("value", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(MethodCallExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getArguments().accept(this, new Context("arguments", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getScope().ifPresent(c -> c.accept(this, new Context("scope", arg.indent + 1)));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(MethodDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isDefault", n.isDefault(), arg.indent + 1);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getBody().ifPresent(c -> c.accept(this, new Context("body", arg.indent + 1)));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getParameters().accept(this, new Context("parameters", arg.indent + 1));
        n.getThrownExceptions().accept(this, new Context("thrownExceptions", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getTypeParameters().accept(this, new Context("typeParameters", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(MethodReferenceExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "identifier", n.getIdentifier(), arg.indent + 1);
        n.getScope().accept(this, new Context("scope", arg.indent + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(NameExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(Name n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "identifier", n.getIdentifier(), arg.indent + 1);
        n.getQualifier().ifPresent(c -> c.accept(this, new Context("qualifier", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(NormalAnnotationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getPairs().accept(this, new Context("pairs", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(NullLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ObjectCreationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnonymousClassBody().ifPresent(c -> c.accept(this, new Context("anonymousClassBody", arg.indent + 1)));
        n.getArguments().accept(this, new Context("arguments", arg.indent + 1));
        n.getScope().ifPresent(c -> c.accept(this, new Context("scope", arg.indent + 1)));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, new Context("typeArguments", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(PackageDeclaration n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(Parameter n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "isVarArgs", n.isVarArgs(), arg.indent + 1);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(PrimitiveType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "type", n.getType(), arg.indent + 1);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ReturnStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExpression().ifPresent(c -> c.accept(this, new Context("expression", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SimpleName n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "identifier", n.getIdentifier(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SingleMemberAnnotationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getMemberValue().accept(this, new Context("memberValue", arg.indent + 1));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(StringLiteralExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "value", n.getValue(), arg.indent + 1);
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SuperExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getClassExpr().ifPresent(c -> c.accept(this, new Context("classExpr", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SwitchEntryStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getLabel().ifPresent(c -> c.accept(this, new Context("label", arg.indent + 1)));
        n.getStatements().accept(this, new Context("statements", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SwitchStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getEntries().accept(this, new Context("entries", arg.indent + 1));
        n.getSelector().accept(this, new Context("selector", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(SynchronizedStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ThisExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getClassExpr().ifPresent(c -> c.accept(this, new Context("classExpr", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(ThrowStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(TryStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getCatchClauses().accept(this, new Context("catchClauses", arg.indent + 1));
        n.getFinallyBlock().ifPresent(c -> c.accept(this, new Context("finallyBlock", arg.indent + 1)));
        n.getResources().accept(this, new Context("resources", arg.indent + 1));
        n.getTryBlock().ifPresent(c -> c.accept(this, new Context("tryBlock", arg.indent + 1)));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(TypeExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(TypeParameter n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getTypeBound().accept(this, new Context("typeBound", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(UnaryExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "operator", n.getOperator(), arg.indent + 1);
        n.getExpression().accept(this, new Context("expression", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(UnionType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getElements().accept(this, new Context("elements", arg.indent + 1));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(UnknownType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(VariableDeclarationExpr n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        callback.outputProperty(n, "modifiers", n.getModifiers(), arg.indent + 1);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getVariables().accept(this, new Context("variables", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(VariableDeclarator n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getInitializer().ifPresent(c -> c.accept(this, new Context("initializer", arg.indent + 1)));
        n.getName().accept(this, new Context("name", arg.indent + 1));
        n.getType().accept(this, new Context("type", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(VoidType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(WhileStmt n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getBody().accept(this, new Context("body", arg.indent + 1));
        n.getCondition().accept(this, new Context("condition", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }

    public void visit(WildcardType n, Context arg) {
        callback.enterNode(n, arg.name, arg.indent);
        n.getExtendedTypes().ifPresent(c -> c.accept(this, new Context("extendedTypes", arg.indent + 1)));
        n.getSuperTypes().ifPresent(c -> c.accept(this, new Context("superTypes", arg.indent + 1)));
        n.getAnnotations().accept(this, new Context("annotations", arg.indent + 1));
        n.getComment().ifPresent(c -> c.accept(this, new Context("comment", arg.indent + 1)));
        callback.exitNode(n, arg.name, arg.indent);
    }
}

