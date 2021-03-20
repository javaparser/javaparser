package com.github.javaparser.ast.jml.stmt;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.metamodel.JmlUnreachableStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlUnreachableStmt extends JmlStatement {

    @AllFieldsConstructor
    public JmlUnreachableStmt() {
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
    public boolean isUnreachableStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlUnreachableStmt asUnreachableStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlUnreachableStmt> toUnreachableStmt() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnreachableStmt(Consumer<JmlUnreachableStmt> action) {
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
    public JmlUnreachableStmt clone() {
        return (JmlUnreachableStmt) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlUnreachableStmt(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public boolean isJmlUnreachableStmt() {
        return true;
    }

    @Override
    public JmlUnreachableStmt asJmlUnreachableStmt() {
        return this;
    }

    @Override
    public Optional<JmlUnreachableStmt> toJmlUnreachableStmt() {
        return Optional.of(this);
    }

    public void ifJmlUnreachableStmt(Consumer<JmlUnreachableStmt> action) {
        action.accept(this);
    }

    @Override
    public JmlUnreachableStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlUnreachableStmtMetaModel;
    }
}
