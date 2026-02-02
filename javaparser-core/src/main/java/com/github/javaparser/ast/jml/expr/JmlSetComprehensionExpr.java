package com.github.javaparser.ast.jml.expr;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlSetComprehensionExprMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * 12.5 Set Comprehensions
 * https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC160
 * <p>
 * new JMLObjectSet {Integer i | myIntSet.has(i) &&
 * i != null && 0 <= i.intValue() && i.intValue() <= 10 }
 *
 * @author Alexander Weigl
 * @version 1 (3/20/21)
 */
public class JmlSetComprehensionExpr extends Expression implements Jmlish {

    private VariableDeclarator binding;

    private Expression predicate;

    public JmlSetComprehensionExpr() {}

    @AllFieldsConstructor
    public JmlSetComprehensionExpr(VariableDeclarator binding, Expression predicate) {
        this.binding = binding;
        this.predicate = predicate;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSetComprehensionExpr(TokenRange tokenRange, VariableDeclarator binding, Expression predicate) {
        super(tokenRange);
        setBinding(binding);
        setPredicate(predicate);
        customInitialization();
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSetComprehension() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSetComprehensionExpr asJmlSetComprehension() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSetComprehensionExpr> toJmlSetComprehension() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSetComprehension(Consumer<JmlSetComprehensionExpr> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator getBinding() {
        return binding;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSetComprehensionExpr setBinding(final VariableDeclarator binding) {
        assertNotNull(binding);
        if (binding == this.binding) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BINDING, this.binding, binding);
        if (this.binding != null) this.binding.setParentNode(null);
        this.binding = binding;
        setAsParentNodeOf(binding);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getPredicate() {
        return predicate;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSetComprehensionExpr setPredicate(final Expression predicate) {
        assertNotNull(predicate);
        if (predicate == this.predicate) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PREDICATE, this.predicate, predicate);
        if (this.predicate != null) this.predicate.setParentNode(null);
        this.predicate = predicate;
        setAsParentNodeOf(predicate);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == binding) {
            setBinding((VariableDeclarator) replacementNode);
            return true;
        }
        if (node == predicate) {
            setPredicate((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlSetComprehensionExpr clone() {
        return (JmlSetComprehensionExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlSetComprehensionExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlSetComprehensionExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSetComprehensionExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSetComprehensionExpr asJmlSetComprehensionExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSetComprehensionExpr> toJmlSetComprehensionExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSetComprehensionExpr(Consumer<JmlSetComprehensionExpr> action) {
        action.accept(this);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator binding() {
        return Objects.requireNonNull(binding);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression predicate() {
        return Objects.requireNonNull(predicate);
    }
}
