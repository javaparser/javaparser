package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.LocationSetFunctionMetaModel;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (3/19/21)
 */
public class LocationSetFunction extends LocationSetExpression {

    public enum Function implements JmlKeyword {

        UNION,
        INTERSECT,
        SETMINUS,
        ALL_FIELDS,
        ALL_OBJECTS,
        DISJOINT,
        SUBSET,
        NEW_ELEMS_FRESH;

        private final String symbol;

        Function() {
            symbol = "\\" + name().toLowerCase();
        }

        Function(String symbol) {
            this.symbol = symbol;
        }

        @Override
        public String jmlSymbol() {
            return symbol;
        }
    }

    private Function function;

    private NodeList<LocationSetExpression> arguments;

    public LocationSetFunction() {
        this(Function.UNION, new NodeList<>());
    }

    @AllFieldsConstructor
    public LocationSetFunction(Function function, NodeList<LocationSetExpression> arguments) {
        this(null, function, arguments);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetFunction(TokenRange tokenRange, Function function, NodeList<LocationSetExpression> arguments) {
        super(tokenRange);
        setFunction(function);
        setArguments(arguments);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<LocationSetExpression> getArguments() {
        return arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetFunction setArguments(final NodeList<LocationSetExpression> arguments) {
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
    public Function getFunction() {
        return function;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetFunction setFunction(final Function function) {
        assertNotNull(function);
        if (function == this.function) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.FUNCTION, this.function, function);
        this.function = function;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
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
        if (node == null)
            return false;
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.set(i, (LocationSetExpression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocationSetFunction clone() {
        return (LocationSetFunction) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocationSetFunctionMetaModel getMetaModel() {
        return JavaParserMetaModel.locationSetFunctionMetaModel;
    }
}
