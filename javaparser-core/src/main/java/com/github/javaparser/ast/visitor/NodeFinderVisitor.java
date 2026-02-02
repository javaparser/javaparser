/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import com.github.javaparser.Range;
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
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.body.*;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.stmt.*;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleExportsDirective;
import com.github.javaparser.ast.modules.ModuleOpensDirective;
import com.github.javaparser.ast.modules.ModuleProvidesDirective;
import com.github.javaparser.ast.modules.ModuleRequiresDirective;
import com.github.javaparser.ast.modules.ModuleUsesDirective;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.LocalRecordDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.stmt.YieldStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;
import java.util.function.BiFunction;

/*
 * A visitor who applies a function (based on a range) on each node of the AST and retains the node selected by the function.
 * An example usage might be to find the node that encompasses a range (the covering node).
 */
public class NodeFinderVisitor extends VoidVisitorAdapter<Range> {

    public static BiFunction<Node, Range, Boolean> fConveringNode = (Node n, Range range) -> {
        return n.hasRange() && n.getRange().get().contains(range);
    };

    private Node selectedNode;

    /*
     * A range-based function that is evaluated on each node of the AST until a node
     * matches the function.
     */
    private static BiFunction<Node, Range, Boolean> fn;

    public NodeFinderVisitor(BiFunction<Node, Range, Boolean> fn) {
        this.fn = fn;
    }

    /**
     * Returns the covering node. If more than one nodes are covering the selection,
     * the returned node is last covering node found in a top-down traversal of the
     * AST
     *
     * @return Node
     */
    public Node getSelectedNode() {
        return selectedNode;
    }

    @Override
    public void visit(final AnnotationDeclaration n, final Range arg) {
        {
            n.getMembers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final AnnotationMemberDeclaration n, final Range arg) {
        if (n.getDefaultValue().isPresent()) {
            n.getDefaultValue().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ArrayAccessExpr n, final Range arg) {
        {
            n.getIndex().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ArrayCreationExpr n, final Range arg) {
        {
            n.getElementType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getInitializer().isPresent()) {
            n.getInitializer().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getLevels().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ArrayInitializerExpr n, final Range arg) {
        {
            n.getValues().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final AssertStmt n, final Range arg) {
        {
            n.getCheck().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getMessage().isPresent()) {
            n.getMessage().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final AssignExpr n, final Range arg) {
        {
            n.getTarget().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getValue().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final BinaryExpr n, final Range arg) {
        {
            n.getLeft().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getRight().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final BlockStmt n, final Range arg) {
        {
            n.getStatements().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final BooleanLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final BreakStmt n, final Range arg) {
        if (n.getLabel().isPresent()) {
            n.getLabel().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final CastExpr n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final CatchClause n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getParameter().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final CharLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        return;
    }

    @Override
    public void visit(final ClassExpr n, final Range arg) {
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final Range arg) {
        {
            n.getExtendedTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getImplementedTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getPermittedTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getMembers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ClassOrInterfaceType n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final CompilationUnit n, final Range arg) {
        {
            n.getImports().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getModule().isPresent()) {
            n.getModule().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getPackageDeclaration().isPresent()) {
            n.getPackageDeclaration().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ConditionalExpr n, final Range arg) {
        {
            n.getCondition().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getElseExpr().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getThenExpr().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ConstructorDeclaration n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getReceiverParameter().isPresent()) {
            n.getReceiverParameter().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getThrownExceptions().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ContinueStmt n, final Range arg) {
        if (n.getLabel().isPresent()) {
            n.getLabel().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final DoStmt n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getCondition().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final DoubleLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final EmptyStmt n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final EnclosedExpr n, final Range arg) {
        {
            n.getInner().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final EnumConstantDeclaration n, final Range arg) {
        {
            n.getArguments().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getClassBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final EnumDeclaration n, final Range arg) {
        {
            n.getEntries().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getImplementedTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getMembers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ExplicitConstructorInvocationStmt n, final Range arg) {
        {
            n.getArguments().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getExpression().isPresent()) {
            n.getExpression().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ExpressionStmt n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final FieldAccessExpr n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getScope().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final FieldDeclaration n, final Range arg) {
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getVariables().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ForEachStmt n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getIterable().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getVariable().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ForStmt n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getCompare().isPresent()) {
            n.getCompare().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getInitialization().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getUpdate().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final IfStmt n, final Range arg) {
        {
            n.getCondition().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getElseStmt().isPresent()) {
            n.getElseStmt().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getThenStmt().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final InitializerDeclaration n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final InstanceOfExpr n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getPattern().isPresent()) {
            n.getPattern().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final IntegerLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        return;
    }

    @Override
    public void visit(final JavadocComment n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LabeledStmt n, final Range arg) {
        {
            n.getLabel().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getStatement().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LongLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final MarkerAnnotationExpr n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final MemberValuePair n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getValue().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final MethodCallExpr n, final Range arg) {
        {
            n.getArguments().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final MethodDeclaration n, final Range arg) {
        if (n.getBody().isPresent()) {
            n.getBody().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getReceiverParameter().isPresent()) {
            n.getReceiverParameter().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getThrownExceptions().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final NameExpr n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final NormalAnnotationExpr n, final Range arg) {
        {
            n.getPairs().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final NullLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ObjectCreationExpr n, final Range arg) {
        if (n.getAnonymousClassBody().isPresent()) {
            n.getAnonymousClassBody().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getArguments().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final PackageDeclaration n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final Parameter n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getVarArgsAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final PrimitiveType n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final Name n, final Range arg) {
        if (n.getQualifier().isPresent()) {
            n.getQualifier().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SimpleName n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ArrayType n, final Range arg) {
        {
            n.getComponentType().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ArrayCreationLevel n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getDimension().isPresent()) {
            n.getDimension().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final IntersectionType n, final Range arg) {
        {
            n.getElements().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final UnionType n, final Range arg) {
        {
            n.getElements().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ReturnStmt n, final Range arg) {
        if (n.getExpression().isPresent()) {
            n.getExpression().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SingleMemberAnnotationExpr n, final Range arg) {
        {
            n.getMemberValue().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final StringLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SuperExpr n, final Range arg) {
        if (n.getTypeName().isPresent()) {
            n.getTypeName().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SwitchEntry n, final Range arg) {
        {
            n.getLabels().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getStatements().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getGuard().isPresent()) {
            n.getGuard().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SwitchStmt n, final Range arg) {
        {
            n.getEntries().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getSelector().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SynchronizedStmt n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ThisExpr n, final Range arg) {
        if (n.getTypeName().isPresent()) {
            n.getTypeName().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ThrowStmt n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final TryStmt n, final Range arg) {
        {
            n.getCatchClauses().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getFinallyBlock().isPresent()) {
            n.getFinallyBlock().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getResources().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTryBlock().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LocalClassDeclarationStmt n, final Range arg) {
        {
            n.getClassDeclaration().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LocalRecordDeclarationStmt n, final Range arg) {
        {
            n.getRecordDeclaration().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final TypeParameter n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeBound().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final UnaryExpr n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final UnknownType n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final VariableDeclarationExpr n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getVariables().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final VariableDeclarator n, final Range arg) {
        if (n.getInitializer().isPresent()) {
            n.getInitializer().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final VoidType n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final WhileStmt n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getCondition().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final WildcardType n, final Range arg) {
        if (n.getExtendedType().isPresent()) {
            n.getExtendedType().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getSuperType().isPresent()) {
            n.getSuperType().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LambdaExpr n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final MethodReferenceExpr n, final Range arg) {
        {
            n.getScope().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getTypeArguments().isPresent()) {
            n.getTypeArguments().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final TypeExpr n, final Range arg) {
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ImportDeclaration n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final BlockComment n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final LineComment n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(NodeList n, final Range arg) {
        for (final Object v : n) {
            ((Node) v).accept(this, arg);
        }
        return;
    }

    @Override
    public void visit(final ModuleDeclaration n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getDirectives().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ModuleRequiresDirective n, final Range arg) {
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override()
    public void visit(final ModuleExportsDirective n, final Range arg) {
        {
            n.getModuleNames().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override()
    public void visit(final ModuleProvidesDirective n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getWith().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override()
    public void visit(final ModuleUsesDirective n, final Range arg) {
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ModuleOpensDirective n, final Range arg) {
        {
            n.getModuleNames().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final UnparsableStmt n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final ReceiverParameter n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final VarType n, final Range arg) {
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final Modifier n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final SwitchExpr n, final Range arg) {
        {
            n.getEntries().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getSelector().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final YieldStmt n, final Range arg) {
        {
            n.getExpression().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final TextBlockLiteralExpr n, final Range arg) {
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final TypePatternExpr n, final Range arg) {
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getType().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final RecordDeclaration n, final Range arg) {
        {
            n.getImplementedTypes().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getReceiverParameter().isPresent()) {
            n.getReceiverParameter().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getMembers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }

    @Override
    public void visit(final CompactConstructorDeclaration n, final Range arg) {
        {
            n.getBody().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getModifiers().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getName().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getThrownExceptions().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getTypeParameters().accept(this, arg);
            if (selectedNode != null) return;
        }
        {
            n.getAnnotations().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (n.getComment().isPresent()) {
            n.getComment().get().accept(this, arg);
            if (selectedNode != null) return;
        }
        if (fn.apply(n, arg)) {
            selectedNode = n;
        }
        return;
    }
}
