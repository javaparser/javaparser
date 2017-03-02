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

import java.util.EnumSet;
import java.util.List;
import java.util.stream.Collectors;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EmptyMemberDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.format.FormatInstructions;
import com.github.javaparser.utils.format.FormatInstructionsFactory;

/**
 * A visitor that creates a formatted visualization of the AST as a string.
 * This visitor expects a {@link FormatInstructions} to be supplied to specify how
 * to format the AST. If none is provided, a default implementation is used. The
 * resultant string is retrieved calling {@link #getResult()}, which calls
 * {@link FormatInstructions#postProcess(String)} before returning.
 *
 * @see TreeStructureVisitorGenerator
 * @see FormatInstructions
 * @see BaseNodeMetaModel
 * @see PropertyMetaModel
 * @version 3.1.0
 * @since 3.1.0
 * @author Danny van Bruggen
 * @author Ryan Beckett
 */
public class TreeStructureVisitor extends VoidVisitorAdapter<Integer> {

    private FormatInstructions instructions;
    private StringBuilder stringBuilder;
    private boolean useIndent;
    private boolean elementOnNewline;

    /**
     * Create a new tree structure visitor with the default formatting instructions, where each encompassed
     * element (i.e. node or property) is on a new line and is indented one tab further than its parent.
     */
    public TreeStructureVisitor() {
        this(true, true);
    }

    /**
     * Create a new tree structure visitor with the specified formatting instructions, where each encompassed
     * element (i.e. node or property) is on a new line and is indented one tab further than its parent.
     *
     * @param instructions The formatting instructions to apply.
     */
    public TreeStructureVisitor(FormatInstructions instructions) {
        this(instructions, true, true);
    }

    /**
     * Create a new tree structure visitor with the default formatting instructions, and the specified indentation
     * and new line options.
     *
     * @param useIndent <i>True</i> if each compassed element (i.e. node or property) is indented one tab
     *            further than its parent.
     * @param elementOnNewline <i>True</i> if each compassed element (i.e. node or property) is on a new line.
     */
    public TreeStructureVisitor(boolean useIndent, boolean elementOnNewline) {
        this(FormatInstructionsFactory.getFormatInstructions(), useIndent, elementOnNewline);
    }

    /**
     * Create a new tree structure visitor with the specified formatting instructions, and the specified indentation
     * and new line options.
     *
     * @param instructions The formatting instructions to apply.
     * @param useIndent <i>True</i> if each compassed element (i.e. node or property) is indented one tab
     *            further than its parent.
     * @param elementOnNewline <i>True</i> if each compassed element (i.e. node or property) is on a new line.
     */
    public TreeStructureVisitor(FormatInstructions instructions, boolean useIndent, boolean elementOnNewline) {
        this.instructions = instructions;
        this.stringBuilder = new StringBuilder();
        this.useIndent = useIndent;
        this.elementOnNewline = elementOnNewline;
    }

    /**
     * Get the resultant formatted string generated from running this visitor.
     * {@link FormatInstructions#postProcess(String)}
     * is called before returning from this method.
     *
     * @return The resultant formatted string after post-processing.
     */
    public String getResult() {
        return instructions.postProcess(stringBuilder.toString());
    }

    protected void appendToBuilder(int indentLevel, String text) {
        if (text.isEmpty())
            return;
        if (useIndent) {
            for (int i = 0; i < indentLevel; i++) {
                stringBuilder.append("\t");
            }
        }
        if (elementOnNewline)
            stringBuilder.append(text + "\n");
        else
            stringBuilder.append(text);
    }

    protected void exitNode(Node n, Integer indent) {
        appendToBuilder(indent, instructions.exitNode(n));
    }

    protected void enterNode(Node n, Integer indent) {
        appendToBuilder(indent, instructions.enterNode(n));
    }

    protected void outputProperty(Node node, String name, EnumSet<Modifier> modifiers, Integer indent) {
        List<String> contents = modifiers.stream().map(Enum::name).collect(Collectors.toList());
        appendToBuilder(indent, instructions.outputProperty(node, name, contents));
    }

    protected void outputProperty(Node node, String name, String content, Integer indent) {
        appendToBuilder(indent, instructions.outputProperty(node, name, content));
    }

    protected void outputProperty(Node node, String name, Enum<?> e, Integer indent) {
        outputProperty(node, name, e.toString(), indent);
    }

    protected void outputProperty(Node node, String name, boolean value, Integer indent) {
        outputProperty(node, name, Boolean.toString(value), indent);
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
        outputProperty(n, "isDefault", n.isDefault(), arg + 1);
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
}
