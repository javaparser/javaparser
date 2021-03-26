package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlSetComprehensionMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

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
public class JmlSetComprehension extends Expression implements Jmlish {

    private VariableDeclarator binding;

    private Expression predicate;

    public JmlSetComprehension() {
    }

    @AllFieldsConstructor
    public JmlSetComprehension(VariableDeclarator binding, Expression predicate) {
        this.binding = binding;
        this.predicate = predicate;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSetComprehension(TokenRange tokenRange, VariableDeclarator binding, Expression predicate) {
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
    public JmlSetComprehension asJmlSetComprehension() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSetComprehension> toJmlSetComprehension() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSetComprehension(Consumer<JmlSetComprehension> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator getBinding() {
        return binding;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSetComprehension setBinding(final VariableDeclarator binding) {
        assertNotNull(binding);
        if (binding == this.binding) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BINDING, this.binding, binding);
        if (this.binding != null)
            this.binding.setParentNode(null);
        this.binding = binding;
        setAsParentNodeOf(binding);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getPredicate() {
        return predicate;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSetComprehension setPredicate(final Expression predicate) {
        assertNotNull(predicate);
        if (predicate == this.predicate) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PREDICATE, this.predicate, predicate);
        if (this.predicate != null)
            this.predicate.setParentNode(null);
        this.predicate = predicate;
        setAsParentNodeOf(predicate);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
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
    public JmlSetComprehension clone() {
        return (JmlSetComprehension) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlSetComprehensionMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlSetComprehensionMetaModel;
    }
}
