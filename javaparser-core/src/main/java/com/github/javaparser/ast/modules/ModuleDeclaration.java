package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleDeclarationMetaModel;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;

/**
 * A Java 9 Jigsaw module declaration. <code>@Foo module com.github.abc { requires a.B; }</code>
 */
public final class ModuleDeclaration extends Node implements NodeWithName<ModuleDeclaration>, NodeWithAnnotations<ModuleDeclaration> {

    private Name name;

    private NodeList<AnnotationExpr> annotations;

    private boolean isOpen;

    private NodeList<ModuleStmt> moduleStmts;

    public ModuleDeclaration() {
        this(null, new NodeList<>(), new Name(), false, new NodeList<>());
    }

    public ModuleDeclaration(Name name, boolean isOpen) {
        this(null, new NodeList<>(), name, isOpen, new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleDeclaration(NodeList<AnnotationExpr> annotations, Name name, boolean isOpen, NodeList<ModuleStmt> moduleStmts) {
        this(null, annotations, name, isOpen, moduleStmts);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, Name name, boolean isOpen, NodeList<ModuleStmt> moduleStmts) {
        super(tokenRange);
        setAnnotations(annotations);
        setName(name);
        setOpen(isOpen);
        setModuleStmts(moduleStmts);
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
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return (ModuleDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        for (int i = 0; i < moduleStmts.size(); i++) {
            if (moduleStmts.get(i) == node) {
                moduleStmts.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isOpen() {
        return isOpen;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setOpen(final boolean isOpen) {
        if (isOpen == this.isOpen) {
            return (ModuleDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.OPEN, this.isOpen, isOpen);
        this.isOpen = isOpen;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ModuleStmt> getModuleStmts() {
        return moduleStmts;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleDeclaration setModuleStmts(final NodeList<ModuleStmt> moduleStmts) {
        assertNotNull(moduleStmts);
        if (moduleStmts == this.moduleStmts) {
            return (ModuleDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.MODULE_STMTS, this.moduleStmts, moduleStmts);
        if (this.moduleStmts != null)
            this.moduleStmts.setParentNode(null);
        this.moduleStmts = moduleStmts;
        setAsParentNodeOf(moduleStmts);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleDeclaration clone() {
        return (ModuleDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < moduleStmts.size(); i++) {
            if (moduleStmts.get(i) == node) {
                moduleStmts.set(i, (ModuleStmt) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }
}
