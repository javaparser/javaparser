package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.JmlContainer;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlBodyDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/24/21)
 */
public class JmlBodyDeclaration extends BodyDeclaration<JmlBodyDeclaration> implements JmlContainer<JmlBodyDeclaration, JmlClassLevel> {

    private boolean singleLine;

    private NodeList<SimpleName> jmlTags;

    private NodeList<JmlClassLevel> elements;

    @AllFieldsConstructor
    public JmlBodyDeclaration(boolean singleLine, NodeList<SimpleName> jmlTags, NodeList<JmlClassLevel> elements) {
        this(null, singleLine, jmlTags, elements);
    }

    public JmlBodyDeclaration() {
        this(null);
    }

    public JmlBodyDeclaration(TokenRange range) {
        this(range, false, new NodeList<>(), new NodeList<>());
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
    public boolean isJmlBodyDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlBodyDeclaration asJmlBodyDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlBodyDeclaration> toJmlBodyDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlBodyDeclaration(Consumer<JmlBodyDeclaration> action) {
        action.accept(this);
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
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlBodyDeclaration clone() {
        return (JmlBodyDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlBodyDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlBodyDeclarationMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlBodyDeclaration(TokenRange tokenRange, JmlClassLevel wrapped) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlClassLevel> getElements() {
        return elements;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBodyDeclaration setElements(final NodeList<JmlClassLevel> elements) {
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
    public JmlBodyDeclaration setJmlTags(final NodeList<SimpleName> jmlTags) {
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
    public JmlBodyDeclaration setSingleLine(final boolean singleLine) {
        if (singleLine == this.singleLine) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SINGLE_LINE, this.singleLine, singleLine);
        this.singleLine = singleLine;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.set(i, (JmlClassLevel) replacementNode);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlBodyDeclaration(TokenRange tokenRange, boolean singleLine, NodeList<SimpleName> jmlTags, NodeList<JmlClassLevel> elements) {
        super(tokenRange);
        setSingleLine(singleLine);
        setJmlTags(jmlTags);
        setElements(elements);
        customInitialization();
    }
}
