package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

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
import java.util.function.Consumer;
import org.jspecify.annotations.Nullable;

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
        if (this.name != null) this.name.setParentNode(null);
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

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlCallableClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlCallableClause asJmlCallableClause() {
        throw new IllegalStateException(
                f("%s is not JmlCallableClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlCallableClause> toJmlCallableClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlCallableClause(Consumer<JmlCallableClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClauseLabel() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClauseLabel asJmlClauseLabel() {
        throw new IllegalStateException(
                f("%s is not JmlClauseLabel, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClauseLabel> toJmlClauseLabel() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClauseLabel(Consumer<JmlClauseLabel> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlForallClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlForallClause asJmlForallClause() {
        throw new IllegalStateException(
                f("%s is not JmlForallClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlForallClause> toJmlForallClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlForallClause(Consumer<JmlForallClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlMultiExprClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlMultiExprClause asJmlMultiExprClause() {
        throw new IllegalStateException(f(
                "%s is not JmlMultiExprClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlMultiExprClause> toJmlMultiExprClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlMultiExprClause(Consumer<JmlMultiExprClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlOldClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlOldClause asJmlOldClause() {
        throw new IllegalStateException(
                f("%s is not JmlOldClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlOldClause> toJmlOldClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlOldClause(Consumer<JmlOldClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSignalsClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSignalsClause asJmlSignalsClause() {
        throw new IllegalStateException(
                f("%s is not JmlSignalsClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSignalsClause> toJmlSignalsClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSignalsClause(Consumer<JmlSignalsClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSignalsOnlyClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSignalsOnlyClause asJmlSignalsOnlyClause() {
        throw new IllegalStateException(f(
                "%s is not JmlSignalsOnlyClause, it is %s",
                this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSignalsOnlyClause> toJmlSignalsOnlyClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSignalsOnlyClause(Consumer<JmlSignalsOnlyClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSimpleExprClause() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSimpleExprClause asJmlSimpleExprClause() {
        throw new IllegalStateException(f(
                "%s is not JmlSimpleExprClause, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSimpleExprClause> toJmlSimpleExprClause() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSimpleExprClause(Consumer<JmlSimpleExprClause> action) {}

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClauseIf() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClauseIf asJmlClauseIf() {
        throw new IllegalStateException(
                f("%s is not JmlClauseIf, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClauseIf> toJmlClauseIf() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClauseIf(Consumer<JmlClauseIf> action) {}

    @Nullable()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName name() {
        return name;
    }
}
