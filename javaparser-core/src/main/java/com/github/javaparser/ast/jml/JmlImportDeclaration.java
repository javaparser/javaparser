package com.github.javaparser.ast.jml;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlImportDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/21)
 */
public class JmlImportDeclaration extends Node implements NodeWithName<JmlImportDeclaration>, Jmlish, HasJmlTags<JmlImportDeclaration> {

    private Name name;

    private boolean isStatic, isAsterisk;

    private NodeList<SimpleName> jmlTags = new NodeList<>();

    @AllFieldsConstructor
    public JmlImportDeclaration(Name name, boolean isStatic, boolean isAsterisk) {
        this(null, name, isStatic, isAsterisk);
    }

    public JmlImportDeclaration(Name name, boolean isStatic, boolean isAsterisk, NodeList<SimpleName> jmltags) {
        this(null, name, isStatic, isAsterisk);
        this.jmlTags = jmltags;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlImportDeclaration(TokenRange tokenRange, Name name, boolean isStatic, boolean isAsterisk) {
        super(tokenRange);
        setName(name);
        setStatic(isStatic);
        setAsterisk(isAsterisk);
        customInitialization();
    }

    public JmlImportDeclaration(TokenRange range, ImportDeclaration in, DefaultJmlContainer c) {
        super(range);
        jmlTags = c.getJmlTags();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlImportDeclaration setJmlTags(final NodeList<SimpleName> jmlTags) {
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
    public NodeList<SimpleName> getJmlTags() {
        return jmlTags;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlImportDeclaration setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isAsterisk() {
        return isAsterisk;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlImportDeclaration setAsterisk(final boolean isAsterisk) {
        if (isAsterisk == this.isAsterisk) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.ASTERISK, this.isAsterisk, isAsterisk);
        this.isAsterisk = isAsterisk;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isStatic() {
        return isStatic;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlImportDeclaration setStatic(final boolean isStatic) {
        if (isStatic == this.isStatic) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STATIC, this.isStatic, isStatic);
        this.isStatic = isStatic;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
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
        for (int i = 0; i < jmlTags.size(); i++) {
            if (jmlTags.get(i) == node) {
                jmlTags.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlImportDeclaration clone() {
        return (JmlImportDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlImportDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlImportDeclarationMetaModel;
    }
}
