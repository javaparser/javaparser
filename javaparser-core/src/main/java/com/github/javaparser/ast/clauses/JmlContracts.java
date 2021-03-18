package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Set;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlContractsMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/17/21)
 */
public class JmlContracts extends Node implements Jmlish {

    private boolean singleLine;

    private Set<String> jmlTags;

    private NodeList<JmlContract> elements;

    public JmlContracts(TokenRange tokenRange) {
        super(tokenRange);
    }

    @AllFieldsConstructor
    public JmlContracts(boolean singleLine, Set<String> jmlTags, NodeList<JmlContract> elements) {
        this(null, singleLine, jmlTags, elements);
    }

    @Generated("")
    public JmlContracts(TokenRange tokenRange, boolean singleLine, Set<String> jmlTags, NodeList<JmlContract> elements) {
        super(tokenRange);
        this.singleLine = singleLine;
        this.jmlTags = jmlTags;
        this.elements = elements;
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

    public NodeList<JmlContract> getElements() {
        return elements;
    }

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

    public String getJmlTags() {
        return jmlTags;
    }

    public JmlContracts setJmlTags(final String jmlTags) {
        assertNotNull(jmlTags);
        if (jmlTags == this.jmlTags) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_TAGS, this.jmlTags, jmlTags);
        this.jmlTags = jmlTags;
        return this;
    }

    public boolean isSingleLine() {
        return singleLine;
    }

    public JmlContracts setSingleLine(final boolean singleLine) {
        if (singleLine == this.singleLine) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SINGLE_LINE, this.singleLine, singleLine);
        this.singleLine = singleLine;
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.set(i, (JmlContract) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public JmlContracts clone() {
        return (JmlContracts) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlContractsMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlContractsMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlContracts(TokenRange tokenRange, boolean singleLine, String jmlTags, NodeList<JmlContract> elements) {
        super(tokenRange);
        setSingleLine(singleLine);
        setJmlTags(jmlTags);
        setElements(elements);
        customInitialization();
    }
}
