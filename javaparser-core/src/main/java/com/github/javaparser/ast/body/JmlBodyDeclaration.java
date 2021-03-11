package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlBodyDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/24/21)
 */
public abstract class JmlBodyDeclaration extends BodyDeclaration<JmlBodyDeclaration> implements Jmlish {

    @AllFieldsConstructor
    public JmlBodyDeclaration() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlBodyDeclaration(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public boolean isJmlBodyDeclaration() {
        return true;
    }

    @Override
    public JmlBodyDeclaration asJmlBodyDeclaration() {
        return this;
    }

    @Override
    public Optional<JmlBodyDeclaration> toJmlBodyDeclaration() {
        return Optional.of(this);
    }

    public void ifJmlBodyDeclaration(Consumer<JmlBodyDeclaration> action) {
        action.accept(this);
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
    public JmlBodyDeclaration clone() {
        return (JmlBodyDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlBodyDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlBodyDeclarationMetaModel;
    }
}
