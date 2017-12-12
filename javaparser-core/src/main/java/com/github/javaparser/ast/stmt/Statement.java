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
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import java.util.Optional;

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

    /**
     * This constructor is used by the parser and is considered private.
     */
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
        throw new IllegalStateException(f("%s is not an AssertStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBlockStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BlockStmt asBlockStmt() {
        throw new IllegalStateException(f("%s is not an BlockStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBreakStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public BreakStmt asBreakStmt() {
        throw new IllegalStateException(f("%s is not an BreakStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isContinueStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ContinueStmt asContinueStmt() {
        throw new IllegalStateException(f("%s is not an ContinueStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isDoStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public DoStmt asDoStmt() {
        throw new IllegalStateException(f("%s is not an DoStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEmptyStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EmptyStmt asEmptyStmt() {
        throw new IllegalStateException(f("%s is not an EmptyStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isExplicitConstructorInvocationStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ExplicitConstructorInvocationStmt asExplicitConstructorInvocationStmt() {
        throw new IllegalStateException(f("%s is not an ExplicitConstructorInvocationStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isExpressionStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ExpressionStmt asExpressionStmt() {
        throw new IllegalStateException(f("%s is not an ExpressionStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForStmt asForStmt() {
        throw new IllegalStateException(f("%s is not an ForStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isForeachStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ForeachStmt asForeachStmt() {
        throw new IllegalStateException(f("%s is not an ForeachStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIfStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public IfStmt asIfStmt() {
        throw new IllegalStateException(f("%s is not an IfStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLabeledStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LabeledStmt asLabeledStmt() {
        throw new IllegalStateException(f("%s is not an LabeledStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLocalClassDeclarationStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LocalClassDeclarationStmt asLocalClassDeclarationStmt() {
        throw new IllegalStateException(f("%s is not an LocalClassDeclarationStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isReturnStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ReturnStmt asReturnStmt() {
        throw new IllegalStateException(f("%s is not an ReturnStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchEntryStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchEntryStmt asSwitchEntryStmt() {
        throw new IllegalStateException(f("%s is not an SwitchEntryStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchStmt asSwitchStmt() {
        throw new IllegalStateException(f("%s is not an SwitchStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSynchronizedStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public SynchronizedStmt asSynchronizedStmt() {
        throw new IllegalStateException(f("%s is not an SynchronizedStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isThrowStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ThrowStmt asThrowStmt() {
        throw new IllegalStateException(f("%s is not an ThrowStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTryStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TryStmt asTryStmt() {
        throw new IllegalStateException(f("%s is not an TryStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnparsableStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public UnparsableStmt asUnparsableStmt() {
        throw new IllegalStateException(f("%s is not an UnparsableStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isWhileStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public WhileStmt asWhileStmt() {
        throw new IllegalStateException(f("%s is not an WhileStmt", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAssertStmt(Consumer<AssertStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBlockStmt(Consumer<BlockStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBreakStmt(Consumer<BreakStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifContinueStmt(Consumer<ContinueStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifDoStmt(Consumer<DoStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEmptyStmt(Consumer<EmptyStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifExplicitConstructorInvocationStmt(Consumer<ExplicitConstructorInvocationStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifExpressionStmt(Consumer<ExpressionStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForStmt(Consumer<ForStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifForeachStmt(Consumer<ForeachStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIfStmt(Consumer<IfStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLabeledStmt(Consumer<LabeledStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLocalClassDeclarationStmt(Consumer<LocalClassDeclarationStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifReturnStmt(Consumer<ReturnStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchEntryStmt(Consumer<SwitchEntryStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchStmt(Consumer<SwitchStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSynchronizedStmt(Consumer<SynchronizedStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifThrowStmt(Consumer<ThrowStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTryStmt(Consumer<TryStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnparsableStmt(Consumer<UnparsableStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifWhileStmt(Consumer<WhileStmt> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AssertStmt> toAssertStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BlockStmt> toBlockStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BreakStmt> toBreakStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ContinueStmt> toContinueStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<DoStmt> toDoStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EmptyStmt> toEmptyStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ExplicitConstructorInvocationStmt> toExplicitConstructorInvocationStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ExpressionStmt> toExpressionStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ForStmt> toForStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ForeachStmt> toForeachStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<IfStmt> toIfStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LabeledStmt> toLabeledStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LocalClassDeclarationStmt> toLocalClassDeclarationStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ReturnStmt> toReturnStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchEntryStmt> toSwitchEntryStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchStmt> toSwitchStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SynchronizedStmt> toSynchronizedStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ThrowStmt> toThrowStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TryStmt> toTryStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<UnparsableStmt> toUnparsableStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<WhileStmt> toWhileStmt() {
        return Optional.empty();
    }
}
