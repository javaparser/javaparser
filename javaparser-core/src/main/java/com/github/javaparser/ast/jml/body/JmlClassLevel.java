package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlClassLevelMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (3/17/21)
 */
public abstract class JmlClassLevel<T extends BodyDeclaration<?>> extends BodyDeclaration<T> implements Jmlish {

    @AllFieldsConstructor
    public JmlClassLevel() {
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassLevel(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClassLevel<?> clone() {
        return (JmlClassLevel<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlClassLevel() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlClassLevel asJmlClassLevel() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlClassLevel> toJmlClassLevel() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlClassLevel(Consumer<JmlClassLevel> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassLevelMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassLevelMetaModel;
    }
}
