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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.StatementMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;

/**
 * A base class for all statements.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Statement extends Node {

    @AllFieldsConstructor
    public Statement() {
        this(null);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Statement(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public Statement clone() {
        return (Statement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public StatementMetaModel getMetaModel() {
        return JavaParserMetaModel.statementMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAssertStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AssertStmt asAssertStmt() {
        return (AssertStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBlockStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BlockStmt asBlockStmt() {
        return (BlockStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBreakStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BreakStmt asBreakStmt() {
        return (BreakStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isContinueStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ContinueStmt asContinueStmt() {
        return (ContinueStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isDoStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public DoStmt asDoStmt() {
        return (DoStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEmptyStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EmptyStmt asEmptyStmt() {
        return (EmptyStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isExplicitConstructorInvocationStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ExplicitConstructorInvocationStmt asExplicitConstructorInvocationStmt() {
        return (ExplicitConstructorInvocationStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isExpressionStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ExpressionStmt asExpressionStmt() {
        return (ExpressionStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForStmt asForStmt() {
        return (ForStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForeachStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForeachStmt asForeachStmt() {
        return (ForeachStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIfStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public IfStmt asIfStmt() {
        return (IfStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLabeledStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LabeledStmt asLabeledStmt() {
        return (LabeledStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLocalClassDeclarationStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LocalClassDeclarationStmt asLocalClassDeclarationStmt() {
        return (LocalClassDeclarationStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isReturnStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ReturnStmt asReturnStmt() {
        return (ReturnStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchEntryStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchEntryStmt asSwitchEntryStmt() {
        return (SwitchEntryStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchStmt asSwitchStmt() {
        return (SwitchStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSynchronizedStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SynchronizedStmt asSynchronizedStmt() {
        return (SynchronizedStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isThrowStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ThrowStmt asThrowStmt() {
        return (ThrowStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTryStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TryStmt asTryStmt() {
        return (TryStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnparsableStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public UnparsableStmt asUnparsableStmt() {
        return (UnparsableStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isWhileStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public WhileStmt asWhileStmt() {
        return (WhileStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAssertStmt(Consumer<AssertStmt> action) {
        if (isAssertStmt()) {
            action.accept(asAssertStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBlockStmt(Consumer<BlockStmt> action) {
        if (isBlockStmt()) {
            action.accept(asBlockStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBreakStmt(Consumer<BreakStmt> action) {
        if (isBreakStmt()) {
            action.accept(asBreakStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifContinueStmt(Consumer<ContinueStmt> action) {
        if (isContinueStmt()) {
            action.accept(asContinueStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifDoStmt(Consumer<DoStmt> action) {
        if (isDoStmt()) {
            action.accept(asDoStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEmptyStmt(Consumer<EmptyStmt> action) {
        if (isEmptyStmt()) {
            action.accept(asEmptyStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifExplicitConstructorInvocationStmt(Consumer<ExplicitConstructorInvocationStmt> action) {
        if (isExplicitConstructorInvocationStmt()) {
            action.accept(asExplicitConstructorInvocationStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifExpressionStmt(Consumer<ExpressionStmt> action) {
        if (isExpressionStmt()) {
            action.accept(asExpressionStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForStmt(Consumer<ForStmt> action) {
        if (isForStmt()) {
            action.accept(asForStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForeachStmt(Consumer<ForeachStmt> action) {
        if (isForeachStmt()) {
            action.accept(asForeachStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIfStmt(Consumer<IfStmt> action) {
        if (isIfStmt()) {
            action.accept(asIfStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLabeledStmt(Consumer<LabeledStmt> action) {
        if (isLabeledStmt()) {
            action.accept(asLabeledStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLocalClassDeclarationStmt(Consumer<LocalClassDeclarationStmt> action) {
        if (isLocalClassDeclarationStmt()) {
            action.accept(asLocalClassDeclarationStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifReturnStmt(Consumer<ReturnStmt> action) {
        if (isReturnStmt()) {
            action.accept(asReturnStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchEntryStmt(Consumer<SwitchEntryStmt> action) {
        if (isSwitchEntryStmt()) {
            action.accept(asSwitchEntryStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchStmt(Consumer<SwitchStmt> action) {
        if (isSwitchStmt()) {
            action.accept(asSwitchStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSynchronizedStmt(Consumer<SynchronizedStmt> action) {
        if (isSynchronizedStmt()) {
            action.accept(asSynchronizedStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifThrowStmt(Consumer<ThrowStmt> action) {
        if (isThrowStmt()) {
            action.accept(asThrowStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTryStmt(Consumer<TryStmt> action) {
        if (isTryStmt()) {
            action.accept(asTryStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnparsableStmt(Consumer<UnparsableStmt> action) {
        if (isUnparsableStmt()) {
            action.accept(asUnparsableStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifWhileStmt(Consumer<WhileStmt> action) {
        if (isWhileStmt()) {
            action.accept(asWhileStmt());
        }
    }
}
