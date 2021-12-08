package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlDocDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocDeclaration extends BodyDeclaration<JmlDocDeclaration> {

    private NodeList<JmlDoc> jmlComments;

    @AllFieldsConstructor
    public JmlDocDeclaration(NodeList<JmlDoc> jmlComments) {
        super((TokenRange) null);
        this.jmlComments = jmlComments;
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
    public NodeList<JmlDoc> getJmlComments() {
        return jmlComments;
    }

    public void setJmlComments(List<JavaToken> jmlComments) {
        // this.jmlComments = jmlComments;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlDocDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlDocDeclaration asJmlDocDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlDocDeclaration> toJmlDocDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlDocDeclaration(Consumer<JmlDocDeclaration> action) {
        action.accept(this);
    }

    public JmlDocDeclaration setJmlComments(final JavaToken jmlComments) {
        assertNotNull(jmlComments);
        notifyPropertyChange(ObservableProperty.JML_COMMENTS, this.jmlComments, jmlComments);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.remove(i);
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
        for (int i = 0; i < jmlComments.size(); i++) {
            if (jmlComments.get(i) == node) {
                jmlComments.set(i, (JmlDoc) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlDocDeclaration clone() {
        return (JmlDocDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlDocDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlDocDeclarationMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlDocDeclaration(TokenRange tokenRange, JavaToken jmlComments) {
        super(tokenRange);
        setJmlComments(jmlComments);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlDocDeclaration setJmlComments(final NodeList<JmlDoc> jmlComments) {
        assertNotNull(jmlComments);
        if (jmlComments == this.jmlComments) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.JML_COMMENTS, this.jmlComments, jmlComments);
        if (this.jmlComments != null)
            this.jmlComments.setParentNode(null);
        this.jmlComments = jmlComments;
        setAsParentNodeOf(jmlComments);
        return this;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlDocDeclaration(TokenRange tokenRange, NodeList<JmlDoc> jmlComments) {
        super(tokenRange);
        setJmlComments(jmlComments);
        customInitialization();
    }
}
