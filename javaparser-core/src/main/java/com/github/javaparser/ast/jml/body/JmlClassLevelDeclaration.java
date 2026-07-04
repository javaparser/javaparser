package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlClassLevelDeclarationMetaModel;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (3/17/21)
 */
public abstract class JmlClassLevelDeclaration<T extends BodyDeclaration<?>> extends BodyDeclaration<T>
        implements Jmlish, NodeWithJmlTags<T> {

    @AllFieldsConstructor
    public JmlClassLevelDeclaration() {}

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassLevelDeclaration(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClassLevelDeclaration<?> clone() {
        return (JmlClassLevelDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassLevelDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassLevelDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClassLevelDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClassLevelDeclaration asJmlClassLevelDeclaration() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClassLevelDeclaration> toJmlClassLevelDeclaration() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClassLevelDeclaration(Consumer<JmlClassLevelDeclaration> action) {
        action.accept(this);
    }
}
