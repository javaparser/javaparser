package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlClauseMetaModel;
import com.github.javaparser.metamodel.OptionalProperty;
import java.util.Optional;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public abstract class JmlClause extends Node implements Jmlish {

    @OptionalProperty
    private SimpleName name;

    public JmlClause() {
        this((SimpleName) null);
    }

    @AllFieldsConstructor
    public JmlClause(final SimpleName name) {
        this(null, name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClause(TokenRange tokenRange, SimpleName name) {
        super(tokenRange);
        setName(name);
        customInitialization();
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClause clone() {
        return (JmlClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClauseMetaModel;
    }

    public abstract JmlClauseKind getKind();

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<SimpleName> getName() {
        return Optional.ofNullable(name);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClause setName(final SimpleName name) {
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public JmlClause removeName() {
        return setName((SimpleName) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        if (name != null) {
            if (node == name) {
                removeName();
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (name != null) {
            if (node == name) {
                setName((SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    public boolean isJmlCallableClause() {
        return false;
    }

    public JmlCallableClause asJmlCallableClause() {
        throw new IllegalStateException(f("%s is not JmlCallableClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlCallableClause> toJmlCallableClause() {
        return Optional.empty();
    }

    public void ifJmlCallableClause(Consumer<JmlCallableClause> action) {
    }

    public boolean isJmlClauseLabel() {
        return false;
    }

    public JmlClauseLabel asJmlClauseLabel() {
        throw new IllegalStateException(f("%s is not JmlClauseLabel, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlClauseLabel> toJmlClauseLabel() {
        return Optional.empty();
    }

    public void ifJmlClauseLabel(Consumer<JmlClauseLabel> action) {
    }

    public boolean isJmlForallClause() {
        return false;
    }

    public JmlForallClause asJmlForallClause() {
        throw new IllegalStateException(f("%s is not JmlForallClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlForallClause> toJmlForallClause() {
        return Optional.empty();
    }

    public void ifJmlForallClause(Consumer<JmlForallClause> action) {
    }

    public boolean isJmlMultiExprClause() {
        return false;
    }

    public JmlMultiExprClause asJmlMultiExprClause() {
        throw new IllegalStateException(f("%s is not JmlMultiExprClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlMultiExprClause> toJmlMultiExprClause() {
        return Optional.empty();
    }

    public void ifJmlMultiExprClause(Consumer<JmlMultiExprClause> action) {
    }

    public boolean isJmlOldClause() {
        return false;
    }

    public JmlOldClause asJmlOldClause() {
        throw new IllegalStateException(f("%s is not JmlOldClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlOldClause> toJmlOldClause() {
        return Optional.empty();
    }

    public void ifJmlOldClause(Consumer<JmlOldClause> action) {
    }

    public boolean isJmlSignalsClause() {
        return false;
    }

    public JmlSignalsClause asJmlSignalsClause() {
        throw new IllegalStateException(f("%s is not JmlSignalsClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlSignalsClause> toJmlSignalsClause() {
        return Optional.empty();
    }

    public void ifJmlSignalsClause(Consumer<JmlSignalsClause> action) {
    }

    public boolean isJmlSignalsOnlyClause() {
        return false;
    }

    public JmlSignalsOnlyClause asJmlSignalsOnlyClause() {
        throw new IllegalStateException(f("%s is not JmlSignalsOnlyClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlSignalsOnlyClause> toJmlSignalsOnlyClause() {
        return Optional.empty();
    }

    public void ifJmlSignalsOnlyClause(Consumer<JmlSignalsOnlyClause> action) {
    }

    public boolean isJmlSimpleExprClause() {
        return false;
    }

    public JmlSimpleExprClause asJmlSimpleExprClause() {
        throw new IllegalStateException(f("%s is not JmlSimpleExprClause, it is %s", this, this.getClass().getSimpleName()));
    }

    public Optional<JmlSimpleExprClause> toJmlSimpleExprClause() {
        return Optional.empty();
    }

    public void ifJmlSimpleExprClause(Consumer<JmlSimpleExprClause> action) {
    }
}
