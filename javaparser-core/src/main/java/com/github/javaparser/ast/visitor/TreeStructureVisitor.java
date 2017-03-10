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
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import java.util.EnumSet;

/**
 * A visitor that creates a simple visualisation of the AST.
 */
public class TreeStructureVisitor extends VoidVisitorAdapter<Integer> {

    protected void printIndented(int indentLevel, String text) {
        for (int i = 0; i < indentLevel; i++) {
            System.out.print("\t");
        }
        System.out.println(text);
    }

    protected void exitNode(Node n, Integer indent) {
    }

    protected void enterNode(Node n, Integer indent) {
        printIndented(indent, n.getClass().getSimpleName());
    }

    protected void outputProperty(Node node, String name, EnumSet<Modifier> modifiers, Integer indent) {
        printIndented(indent, name + ": " + modifiers);
    }

    protected void outputProperty(Node node, String name, Enum<?> e, Integer indent) {
        printIndented(indent, name + ": " + e);
    }

    protected void outputProperty(Node node, String name, String content, Integer indent) {
        printIndented(indent, name + ": " + content);
    }

    protected void outputProperty(Node node, String name, boolean value, Integer indent) {
        printIndented(indent, name + ": " + value);
    }

    @Override
    public void visit(NodeList n, Integer arg) {
        ((NodeList<Node>) n).forEach(x -> x.accept(this, arg));
    }

    public void visit(AnnotationDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getMembers().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(AnnotationMemberDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getDefaultValue().ifPresent(c -> c.accept(this, arg + 1));
        n.getName().accept(this, arg + 1);
        n.getType().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ArrayAccessExpr n, Integer arg) {
        enterNode(n, arg);
        n.getIndex().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ArrayCreationExpr n, Integer arg) {
        enterNode(n, arg);
        n.getElementType().accept(this, arg + 1);
        n.getInitializer().ifPresent(c -> c.accept(this, arg + 1));
        n.getLevels().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ArrayCreationLevel n, Integer arg) {
        enterNode(n, arg);
        n.getAnnotations().accept(this, arg + 1);
        n.getDimension().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ArrayInitializerExpr n, Integer arg) {
        enterNode(n, arg);
        n.getValues().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ArrayType n, Integer arg) {
        enterNode(n, arg);
        n.getComponentType().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(AssertStmt n, Integer arg) {
        enterNode(n, arg);
        n.getCheck().accept(this, arg + 1);
        n.getMessage().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(AssignExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "operator", n.getOperator(), arg + 1);
        n.getTarget().accept(this, arg + 1);
        n.getValue().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(BinaryExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "operator", n.getOperator(), arg + 1);
        n.getLeft().accept(this, arg + 1);
        n.getRight().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(BlockComment n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "content", n.getContent(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(BlockStmt n, Integer arg) {
        enterNode(n, arg);
        n.getStatements().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(BooleanLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(BreakStmt n, Integer arg) {
        enterNode(n, arg);
        n.getLabel().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(CastExpr n, Integer arg) {
        enterNode(n, arg);
        n.getExpression().accept(this, arg + 1);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(CatchClause n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getParameter().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(CharLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ClassExpr n, Integer arg) {
        enterNode(n, arg);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ClassOrInterfaceDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isInterface", n.isInterface(), arg + 1);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getExtendedTypes().accept(this, arg + 1);
        n.getImplementedTypes().accept(this, arg + 1);
        n.getTypeParameters().accept(this, arg + 1);
        n.getMembers().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ClassOrInterfaceType n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getScope().ifPresent(c -> c.accept(this, arg + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(CompilationUnit n, Integer arg) {
        enterNode(n, arg);
        n.getImports().accept(this, arg + 1);
        n.getModule().ifPresent(c -> c.accept(this, arg + 1));
        n.getPackageDeclaration().ifPresent(c -> c.accept(this, arg + 1));
        n.getTypes().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ConditionalExpr n, Integer arg) {
        enterNode(n, arg);
        n.getCondition().accept(this, arg + 1);
        n.getElseExpr().accept(this, arg + 1);
        n.getThenExpr().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ConstructorDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getBody().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getParameters().accept(this, arg + 1);
        n.getThrownExceptions().accept(this, arg + 1);
        n.getTypeParameters().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ContinueStmt n, Integer arg) {
        enterNode(n, arg);
        n.getLabel().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(DoStmt n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getCondition().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(DoubleLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(EmptyMemberDeclaration n, Integer arg) {
        enterNode(n, arg);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(EmptyStmt n, Integer arg) {
        enterNode(n, arg);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(EnclosedExpr n, Integer arg) {
        enterNode(n, arg);
        n.getInner().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(EnumConstantDeclaration n, Integer arg) {
        enterNode(n, arg);
        n.getArguments().accept(this, arg + 1);
        n.getClassBody().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(EnumDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getEntries().accept(this, arg + 1);
        n.getImplementedTypes().accept(this, arg + 1);
        n.getMembers().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ExplicitConstructorInvocationStmt n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isThis", n.isThis(), arg + 1);
        n.getArguments().accept(this, arg + 1);
        n.getExpression().ifPresent(c -> c.accept(this, arg + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ExpressionStmt n, Integer arg) {
        enterNode(n, arg);
        n.getExpression().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(FieldAccessExpr n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getScope().ifPresent(c -> c.accept(this, arg + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(FieldDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getVariables().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ForStmt n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getCompare().ifPresent(c -> c.accept(this, arg + 1));
        n.getInitialization().accept(this, arg + 1);
        n.getUpdate().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ForeachStmt n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getIterable().accept(this, arg + 1);
        n.getVariable().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(IfStmt n, Integer arg) {
        enterNode(n, arg);
        n.getCondition().accept(this, arg + 1);
        n.getElseStmt().ifPresent(c -> c.accept(this, arg + 1));
        n.getThenStmt().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ImportDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isAsterisk", n.isAsterisk(), arg + 1);
        outputProperty(n, "isStatic", n.isStatic(), arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(InitializerDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isStatic", n.isStatic(), arg + 1);
        n.getBody().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(InstanceOfExpr n, Integer arg) {
        enterNode(n, arg);
        n.getExpression().accept(this, arg + 1);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(IntegerLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(IntersectionType n, Integer arg) {
        enterNode(n, arg);
        n.getElements().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(JavadocComment n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "content", n.getContent(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(LabeledStmt n, Integer arg) {
        enterNode(n, arg);
        n.getLabel().accept(this, arg + 1);
        n.getStatement().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(LambdaExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isEnclosingParameters", n.isEnclosingParameters(), arg + 1);
        n.getBody().accept(this, arg + 1);
        n.getParameters().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(LineComment n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "content", n.getContent(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(LocalClassDeclarationStmt n, Integer arg) {
        enterNode(n, arg);
        n.getClassDeclaration().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(LongLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(MarkerAnnotationExpr n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(MemberValuePair n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getValue().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(MethodCallExpr n, Integer arg) {
        enterNode(n, arg);
        n.getArguments().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getScope().ifPresent(c -> c.accept(this, arg + 1));
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(MethodDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getBody().ifPresent(c -> c.accept(this, arg + 1));
        n.getType().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getParameters().accept(this, arg + 1);
        n.getThrownExceptions().accept(this, arg + 1);
        n.getTypeParameters().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(MethodReferenceExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "identifier", n.getIdentifier(), arg + 1);
        n.getScope().accept(this, arg + 1);
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(NameExpr n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(Name n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "identifier", n.getIdentifier(), arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getQualifier().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(NormalAnnotationExpr n, Integer arg) {
        enterNode(n, arg);
        n.getPairs().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(NullLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ObjectCreationExpr n, Integer arg) {
        enterNode(n, arg);
        n.getAnonymousClassBody().ifPresent(c -> c.accept(this, arg + 1));
        n.getArguments().accept(this, arg + 1);
        n.getScope().ifPresent(c -> c.accept(this, arg + 1));
        n.getType().accept(this, arg + 1);
        n.getTypeArguments().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(PackageDeclaration n, Integer arg) {
        enterNode(n, arg);
        n.getAnnotations().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(Parameter n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isVarArgs", n.isVarArgs(), arg + 1);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getType().accept(this, arg + 1);
        n.getVarArgsAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(PrimitiveType n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "type", n.getType(), arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ReturnStmt n, Integer arg) {
        enterNode(n, arg);
        n.getExpression().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SimpleName n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "identifier", n.getIdentifier(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SingleMemberAnnotationExpr n, Integer arg) {
        enterNode(n, arg);
        n.getMemberValue().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(StringLiteralExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "value", n.getValue(), arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SuperExpr n, Integer arg) {
        enterNode(n, arg);
        n.getClassExpr().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SwitchEntryStmt n, Integer arg) {
        enterNode(n, arg);
        n.getLabel().ifPresent(c -> c.accept(this, arg + 1));
        n.getStatements().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SwitchStmt n, Integer arg) {
        enterNode(n, arg);
        n.getEntries().accept(this, arg + 1);
        n.getSelector().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(SynchronizedStmt n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getExpression().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ThisExpr n, Integer arg) {
        enterNode(n, arg);
        n.getClassExpr().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ThrowStmt n, Integer arg) {
        enterNode(n, arg);
        n.getExpression().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(TryStmt n, Integer arg) {
        enterNode(n, arg);
        n.getCatchClauses().accept(this, arg + 1);
        n.getFinallyBlock().ifPresent(c -> c.accept(this, arg + 1));
        n.getResources().accept(this, arg + 1);
        n.getTryBlock().ifPresent(c -> c.accept(this, arg + 1));
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(TypeExpr n, Integer arg) {
        enterNode(n, arg);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(TypeParameter n, Integer arg) {
        enterNode(n, arg);
        n.getName().accept(this, arg + 1);
        n.getTypeBound().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(UnaryExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "operator", n.getOperator(), arg + 1);
        n.getExpression().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(UnionType n, Integer arg) {
        enterNode(n, arg);
        n.getElements().accept(this, arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(UnknownType n, Integer arg) {
        enterNode(n, arg);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(VariableDeclarationExpr n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getVariables().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(VariableDeclarator n, Integer arg) {
        enterNode(n, arg);
        n.getInitializer().ifPresent(c -> c.accept(this, arg + 1));
        n.getName().accept(this, arg + 1);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(VoidType n, Integer arg) {
        enterNode(n, arg);
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(WhileStmt n, Integer arg) {
        enterNode(n, arg);
        n.getBody().accept(this, arg + 1);
        n.getCondition().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(WildcardType n, Integer arg) {
        enterNode(n, arg);
        n.getExtendedType().ifPresent(c -> c.accept(this, arg + 1));
        n.getSuperType().ifPresent(c -> c.accept(this, arg + 1));
        n.getAnnotations().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ModuleDeclaration n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "isOpen", n.isOpen(), arg + 1);
        n.getAnnotations().accept(this, arg + 1);
        n.getModuleStmts().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    public void visit(ModuleRequiresStmt n, Integer arg) {
        enterNode(n, arg);
        outputProperty(n, "modifiers", n.getModifiers(), arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    @Override()
    public void visit(ModuleExportsStmt n, Integer arg) {
        enterNode(n, arg);
        n.getModuleNames().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    @Override()
    public void visit(ModuleProvidesStmt n, Integer arg) {
        enterNode(n, arg);
        n.getType().accept(this, arg + 1);
        n.getWithTypes().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    @Override()
    public void visit(ModuleUsesStmt n, Integer arg) {
        enterNode(n, arg);
        n.getType().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }

    @Override
    public void visit(ModuleOpensStmt n, Integer arg) {
        enterNode(n, arg);
        n.getModuleNames().accept(this, arg + 1);
        n.getName().accept(this, arg + 1);
        n.getComment().ifPresent(c -> c.accept(this, arg + 1));
        exitNode(n, arg);
    }
}
