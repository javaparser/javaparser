package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlFunctionMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/22/21)
 */
public class JmlFunction extends Expression implements Jmlish {

    private JmlName functionName;

    private NodeList<Expression> arguments;

    @AllFieldsConstructor
    public JmlFunction(JmlName functionName, NodeList<Expression> arguments) {
        this(null, functionName, arguments);
    }

    public JmlFunction(TokenRange range, JavaToken quant, Expression... arguments) {
        this(range, new JmlName(quant.toTokenRange(), quant.getText()), new NodeList<>(arguments));
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
    public boolean isJmlFunction() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlFunction asJmlFunction() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlFunction> toJmlFunction() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlFunction(Consumer<JmlFunction> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlFunction setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        if (arguments == this.arguments) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null)
            this.arguments.setParentNode(null);
        this.arguments = arguments;
        setAsParentNodeOf(arguments);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlName getFunctionName() {
        return functionName;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlFunction setFunctionName(final JmlName functionName) {
        assertNotNull(functionName);
        if (functionName == this.functionName) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.FUNCTION_NAME, this.functionName, functionName);
        if (this.functionName != null)
            this.functionName.setParentNode(null);
        this.functionName = functionName;
        setAsParentNodeOf(functionName);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.remove(i);
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
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (node == functionName) {
            setFunctionName((JmlName) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlFunction clone() {
        return (JmlFunction) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlFunctionMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlFunctionMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlFunction(TokenRange tokenRange, JmlName functionName, NodeList<Expression> arguments) {
        super(tokenRange);
        setFunctionName(functionName);
        setArguments(arguments);
        customInitialization();
    }
}
