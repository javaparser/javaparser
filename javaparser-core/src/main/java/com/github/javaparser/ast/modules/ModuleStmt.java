package com.github.javaparser.ast.modules;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleStmtMetaModel;
import javax.annotation.Generated;

public abstract class ModuleStmt extends Node {

    @AllFieldsConstructor
    public ModuleStmt() {
        this(null);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleStmt(Range range) {
        super(range);
        customInitialization();
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleStmt clone() {
        return (ModuleStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleStmtMetaModel;
    }
}
