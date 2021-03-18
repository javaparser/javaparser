package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.Set;
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
public class JmlBodyDeclaration extends BodyDeclaration<JmlBodyDeclaration> {

    private boolean singleLine;

    private Set<String> jmlTags;

    private NodeList<JmlClassLevel> elements;

    @AllFieldsConstructor
    public JmlBodyDeclaration(boolean singleLine, Set<String> jmlTags, NodeList<JmlClassLevel> elements) {
        this.singleLine = singleLine;
        this.jmlTags = jmlTags;
        this.elements = elements;
    }

    public JmlBodyDeclaration(TokenRange range, boolean singleLine, Set<String> jmlTags, NodeList<JmlClassLevel> elements) {
        super(range);
        this.singleLine = singleLine;
        this.jmlTags = jmlTags;
        this.elements = elements;
    }

    public JmlBodyDeclaration() {
        this(null);
    }

    public JmlBodyDeclaration(TokenRange range) {
        super(range);
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
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.remove(i);
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
    public String getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBodyDeclaration setJmlTags(final String jmlTags) {
        assertNotNull(jmlTags);
        if (jmlTags == this.jmlTags) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_TAGS, this.jmlTags, jmlTags);
        this.jmlTags = jmlTags;
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
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) == node) {
                elements.set(i, (JmlClassLevel) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlBodyDeclaration(TokenRange tokenRange, boolean singleLine, String jmlTags, NodeList<JmlClassLevel> elements, boolean singleLine, String jmlTags, NodeList<JmlClassLevel> elements) {
        super(tokenRange);
        setSingleLine(singleLine);
        setJmlTags(jmlTags);
        setElements(elements);
        setSingleLine(singleLine);
        setJmlTags(jmlTags);
        setElements(elements);
        customInitialization();
    }
}
