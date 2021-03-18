package com.github.javaparser.ast.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlSetStmtMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.metamodel.JmlRefiningStmtMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlRefiningStmt extends JmlStatement {

    @AllFieldsConstructor
    public JmlRefiningStmt() {
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
    public boolean isJmlRefiningStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlRefiningStmt asJmlRefiningStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlRefiningStmt> toJmlRefiningStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlRefiningStmt(Consumer<JmlRefiningStmt> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlRefiningStmt clone() {
        return (JmlRefiningStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlRefiningStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlRefiningStmtMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlRefiningStmt(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }
}
