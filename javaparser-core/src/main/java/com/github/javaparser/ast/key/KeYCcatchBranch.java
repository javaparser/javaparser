package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeYCcatchBranchMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

public abstract class KeYCcatchBranch extends Node {

    @AllFieldsConstructor
    public KeYCcatchBranch() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeYCcatchBranch(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    public KeYCcatchBranch clone() {
        return (KeYCcatchBranch) accept(new CloneVisitor(), null);
    }

    @Override
    public KeYCcatchBranchMetaModel getMetaModel() {
        return JavaParserMetaModel.keYCcatchBranchMetaModel;
    }
}
