package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlClauseIfMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/22/21)
 */
public class JmlClauseIf extends JmlClause implements MethodContractable {

    private JmlClauseKind kind;

    private Expression then;

    private Expression condition;

    @AllFieldsConstructor
    public JmlClauseIf(SimpleName name, Expression condition, JmlClauseKind kind, Expression then) {
        this(null, name, condition, kind, then);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClauseIf(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == condition) {
            setCondition((Expression) replacementNode);
            return true;
        }
        if (node == then) {
            setThen((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClauseIf clone() {
        return (JmlClauseIf) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind getKind() {
        return kind;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getCondition() {
        return condition;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseIf setCondition(final Expression condition) {
        assertNotNull(condition);
        if (condition == this.condition) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CONDITION, this.condition, condition);
        if (this.condition != null) this.condition.setParentNode(null);
        this.condition = condition;
        setAsParentNodeOf(condition);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseIf setKind(final JmlClauseKind kind) {
        assertNotNull(kind);
        if (kind == this.kind) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KIND, this.kind, kind);
        this.kind = kind;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getThen() {
        return then;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseIf setThen(final Expression then) {
        assertNotNull(then);
        if (then == this.then) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.THEN, this.then, then);
        if (this.then != null) this.then.setParentNode(null);
        this.then = then;
        setAsParentNodeOf(then);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClauseIf() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClauseIf asJmlClauseIf() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClauseIf> toJmlClauseIf() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClauseIf(Consumer<JmlClauseIf> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClauseIfMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClauseIfMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClauseIf(
            TokenRange tokenRange, SimpleName name, Expression condition, JmlClauseKind kind, Expression then) {
        super(tokenRange, name);
        setCondition(condition);
        setKind(kind);
        setThen(then);
        customInitialization();
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression condition() {
        return Objects.requireNonNull(condition);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClauseKind kind() {
        return Objects.requireNonNull(kind);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression then() {
        return Objects.requireNonNull(then);
    }
}
