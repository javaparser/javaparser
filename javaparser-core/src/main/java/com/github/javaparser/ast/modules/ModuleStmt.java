package com.github.javaparser.ast.modules;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleStmtMetaModel;

public abstract class ModuleStmt extends Node {

    public ModuleStmt(Range range) {
        super(range);
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public ModuleStmt clone() {
        return (ModuleStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ModuleStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleStmtMetaModel;
    }
}
