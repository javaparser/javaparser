package com.github.javaparser.ast.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.Node;
import javax.annotation.Generated;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.UnparsableStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A statement that had parse errors.
 * Nothing is known about it except the tokens it covers.
 */
public class UnparsableStmt extends Statement {

    @AllFieldsConstructor
    public UnparsableStmt() {
        this(null);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public UnparsableStmt(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }
    
    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public UnparsableStmt clone() {
        return (UnparsableStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public UnparsableStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.unparsableStatementMetaModel;
    }
}
