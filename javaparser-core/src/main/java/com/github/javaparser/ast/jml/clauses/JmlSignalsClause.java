package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlSignalsClauseMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlSignalsClause extends JmlClause implements MethodContractable, BlockContractable {

    private Parameter parameter;

    private Expression expression;

    @AllFieldsConstructor
    public JmlSignalsClause(SimpleName name, Parameter parameter, Expression expression) {
        this(null, name, parameter, expression);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSignalsClause(TokenRange tokenRange, SimpleName name, Parameter parameter, Expression expression) {
        super(tokenRange, name);
        setParameter(parameter);
        setExpression(expression);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlSignalsClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSignalsClause setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null) this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlSignalsClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlSignalsClauseMetaModel;
    }

    @Override
    public JmlClauseKind getKind() {
        return JmlClauseKind.SIGNALS;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter getParameter() {
        return parameter;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlSignalsClause setParameter(final Parameter parameter) {
        assertNotNull(parameter);
        if (parameter == this.parameter) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PARAMETER, this.parameter, parameter);
        if (this.parameter != null) this.parameter.setParentNode(null);
        this.parameter = parameter;
        setAsParentNodeOf(parameter);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        if (node == parameter) {
            setParameter((Parameter) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlSignalsClause clone() {
        return (JmlSignalsClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlSignalsClause() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlSignalsClause asJmlSignalsClause() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlSignalsClause> toJmlSignalsClause() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlSignalsClause(Consumer<JmlSignalsClause> action) {
        action.accept(this);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression expression() {
        return Objects.requireNonNull(expression);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter parameter() {
        return Objects.requireNonNull(parameter);
    }
}
