package com.github.javaparser.ast.jml.body;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlClassAccessibleDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlClassAccessibleDeclaration extends JmlClassLevel implements NodeWithModifiers<JmlClassAccessibleDeclaration> {

    private NodeList<Modifier> modifiers;

    private SimpleName label;

    private NodeList<Expression> expressions;

    private Expression measuredBy;

    public JmlClassAccessibleDeclaration() {
        this(null, new NodeList<>(), null, new NodeList<>(), null);
    }

    @AllFieldsConstructor
    public JmlClassAccessibleDeclaration(NodeList<Modifier> modifiers, SimpleName label, NodeList<Expression> expressions, Expression measuredBy) {
        this(null, modifiers, label, expressions, measuredBy);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassAccessibleDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, SimpleName label, NodeList<Expression> expressions, Expression measuredBy) {
        super(tokenRange);
        setModifiers(modifiers);
        setLabel(label);
        setExpressions(expressions);
        setMeasuredBy(measuredBy);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAccessibleDeclaration setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
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
    public JmlClassAccessibleDeclaration(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.remove(i);
                return true;
            }
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
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
        for (int i = 0; i < expressions.size(); i++) {
            if (expressions.get(i) == node) {
                expressions.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (node == label) {
            setLabel((SimpleName) replacementNode);
            return true;
        }
        if (node == measuredBy) {
            setMeasuredBy((Expression) replacementNode);
            return true;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClassAccessibleDeclaration clone() {
        return (JmlClassAccessibleDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassAccessibleDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassAccessibleDeclarationMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExpressions() {
        return expressions;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAccessibleDeclaration setExpressions(final NodeList<Expression> expressions) {
        assertNotNull(expressions);
        if (expressions == this.expressions) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSIONS, this.expressions, expressions);
        if (this.expressions != null)
            this.expressions.setParentNode(null);
        this.expressions = expressions;
        setAsParentNodeOf(expressions);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getLabel() {
        return label;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAccessibleDeclaration setLabel(final SimpleName label) {
        assertNotNull(label);
        if (label == this.label) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.LABEL, this.label, label);
        if (this.label != null)
            this.label.setParentNode(null);
        this.label = label;
        setAsParentNodeOf(label);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getMeasuredBy() {
        return measuredBy;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlClassAccessibleDeclaration setMeasuredBy(final Expression measuredBy) {
        assertNotNull(measuredBy);
        if (measuredBy == this.measuredBy) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MEASURED_BY, this.measuredBy, measuredBy);
        if (this.measuredBy != null)
            this.measuredBy.setParentNode(null);
        this.measuredBy = measuredBy;
        setAsParentNodeOf(measuredBy);
        return this;
    }
}
