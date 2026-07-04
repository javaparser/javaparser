package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlExpressionMetaModel;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (4/6/26)
 */
public abstract class JmlExpression extends Expression implements Jmlish {

    @AllFieldsConstructor
    public JmlExpression() {
        super();
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlExpression(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public boolean isJmlExpression() {
        return true;
    }

    @Override
    public JmlExpression asJmlExpression() {
        return this;
    }

    @Override
    public Optional<JmlExpression> toJmlExpression() {
        return Optional.of(this);
    }

    public void ifJmlExpression(Consumer<JmlExpression> action) {
        action.accept(this);
    }

    @Override
    public JmlExpression clone() {
        return (JmlExpression) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlExpressionMetaModel;
    }
}
