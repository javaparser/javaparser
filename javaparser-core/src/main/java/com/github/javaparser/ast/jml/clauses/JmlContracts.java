package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.JmlContainer;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlContractsMetaModel;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (3/17/21)
 */
public class JmlContracts extends Node implements Jmlish, JmlContainer<JmlContracts, JmlContract> {

    private boolean singleLine;

    private NodeList<SimpleName> jmlTags;

    private NodeList<JmlContract> elements;

    public JmlContracts(TokenRange tokenRange) {
        super(tokenRange);
    }

    @AllFieldsConstructor
    public JmlContracts(boolean singleLine, NodeList<SimpleName> jmlTags, NodeList<JmlContract> elements) {
        this(null, singleLine, jmlTags, elements);
    }

    public JmlContracts() {
        this(false, new NodeList<>(), new NodeList<>());
    }

    public JmlContracts(TokenRange range, NodeList<JmlContract> elements) {
        this(range, true, new NodeList<>(), elements);
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

    public JmlContracts(TokenRange tokenRange, JmlContract elements) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlContract> getElements() {
        return elements;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContracts setElements(final NodeList<JmlContract> elements) {
        assertNotNull(elements);
        if (elements == this.elements) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ELEMENTS, this.elements, elements);
        if (this.elements != null)
            this.elements.setParentNode(null);
        this.elements = elements;
        setAsParentNodeOf(elements);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContracts setJmlTags(final NodeList<SimpleName> jmlTags) {
        assertNotNull(jmlTags);
        if (jmlTags == this.jmlTags) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_TAGS, this.jmlTags, jmlTags);
        if (this.jmlTags != null)
            this.jmlTags.setParentNode(null);
        this.jmlTags = jmlTags;
        setAsParentNodeOf(jmlTags);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isSingleLine() {
        return singleLine;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContracts setSingleLine(final boolean singleLine) {
        if (singleLine == this.singleLine) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SINGLE_LINE, this.singleLine, singleLine);
        this.singleLine = singleLine;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.remove(i);
                return true;
            }
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.remove(i);
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
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.set(i, (JmlContract) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlContracts clone() {
        return (JmlContracts) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlContractsMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlContractsMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlContracts(TokenRange tokenRange, boolean singleLine, NodeList<SimpleName> jmlTags, NodeList<JmlContract> elements) {
        super(tokenRange);
        setSingleLine(singleLine);
        setJmlTags(jmlTags);
        setElements(elements);
        customInitialization();
    }
}
