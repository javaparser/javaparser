/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModifierMetaModel;
import java.util.Arrays;
import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A modifier, like private, public, or volatile.
 */
public class Modifier extends Node {

    public static Modifier publicModifier() {
        return new Modifier(DefaultKeyword.PUBLIC);
    }

    public static Modifier protectedModifier() {
        return new Modifier(DefaultKeyword.PROTECTED);
    }

    public static Modifier privateModifier() {
        return new Modifier(DefaultKeyword.PRIVATE);
    }

    public static Modifier abstractModifier() {
        return new Modifier(DefaultKeyword.ABSTRACT);
    }

    public static Modifier staticModifier() {
        return new Modifier(DefaultKeyword.STATIC);
    }

    public static Modifier finalModifier() {
        return new Modifier(DefaultKeyword.FINAL);
    }

    public static Modifier transientModifier() {
        return new Modifier(DefaultKeyword.TRANSIENT);
    }

    public static Modifier volatileModifier() {
        return new Modifier(DefaultKeyword.VOLATILE);
    }

    public static Modifier synchronizedModifier() {
        return new Modifier(DefaultKeyword.SYNCHRONIZED);
    }

    public static Modifier nativeModifier() {
        return new Modifier(DefaultKeyword.NATIVE);
    }

    public static Modifier strictfpModifier() {
        return new Modifier(DefaultKeyword.STRICTFP);
    }

    public static Modifier transitiveModifier() {
        return new Modifier(DefaultKeyword.TRANSITIVE);
    }

    public static Modifier jmlModelModifier() {
        return new Modifier(DefaultKeyword.JML_MODEL);
    }

    public static Modifier jmlGhostModifier() {
        return new Modifier(DefaultKeyword.JML_GHOST);
    }

    public static Modifier jmlSpecPublicModifier() {
        return new Modifier(DefaultKeyword.JML_SPEC_PUBLIC);
    }

    public static Modifier jmlHelperModifier() {
        return new Modifier(DefaultKeyword.JML_HELPER);
    }

    public static Modifier jmlNullableModifier() {
        return new Modifier(DefaultKeyword.JML_NULLABLE);
    }

    public static Modifier jmlNonNullModifier() {
        return new Modifier(DefaultKeyword.JML_NON_NULL);
    }

    public static Modifier jmlSpecPackageModifier() {
        return new Modifier(DefaultKeyword.JML_SPEC_PACKAGE);
    }

    public static Modifier jmlSpecProtectedModifier() {
        return new Modifier(DefaultKeyword.JML_SPEC_PROTECTED);
    }

    public static Modifier jmlSpecPrivateModifier() {
        return new Modifier(DefaultKeyword.JML_SPEC_PRIVATE);
    }

    public interface Keyword {

        String asString();

        String name();
    }

    /**
     * The Java modifier keywords.
     */
    public enum DefaultKeyword implements Keyword {

        DEFAULT("default"),
        PUBLIC("public"),
        PROTECTED("protected"),
        PRIVATE("private"),
        ABSTRACT("abstract"),
        STATIC("static"),
        FINAL("final"),
        TRANSIENT("transient"),
        VOLATILE("volatile"),
        SYNCHRONIZED("synchronized"),
        NATIVE("native"),
        STRICTFP("strictfp"),
        TRANSITIVE("transitive"),
        // JML
        JML_PURE("pure"),
        JML_STRICTLY_PURE("strictly_pure"),
        JML_HELPER("helper"),
        JML_INSTANCE("instance"),
        JML_NULLABLE_BY_DEFAULT("nullable_by_default"),
        JML_NON_NULL("non_null"),
        JML_NULLABLE("nullable"),
        JML_GHOST("ghost"),
        JML_MODEL("model"),
        JML_SPEC_PUBLIC("spec_public"),
        JML_SPEC_PACKAGE("spec_package"),
        JML_SPEC_PROTECTED("spec_protected"),
        JML_SPEC_PRIVATE("spec_private"),
        JML_NO_STATE("no_state"),
        JML_TWO_STATE("two_state"),
        JML_NON_NULL_BY_DEFAULT("non_null_by_default"),
        JML_NON_NULL_ELEMENTS("nonnullelements"),
        JML_UNPARSABLE_MODIFIERS("<unparsable>");

        private final String codeRepresentation;

        DefaultKeyword(String codeRepresentation) {
            this.codeRepresentation = codeRepresentation;
        }

        /**
         * @return the Java keyword represented by this enum constant.
         */
        @Override
        public String asString() {
            return codeRepresentation;
        }
    }

    private Keyword keyword;

    public Modifier() {
        this(DefaultKeyword.PUBLIC);
    }

    @AllFieldsConstructor
    public Modifier(Keyword keyword) {
        this(null, keyword);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Modifier(TokenRange tokenRange, Keyword keyword) {
        super(tokenRange);
        setKeyword(keyword);
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
    public Keyword getKeyword() {
        return keyword;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Modifier setKeyword(final Keyword keyword) {
        assertNotNull(keyword);
        if (keyword == this.keyword) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.KEYWORD, this.keyword, keyword);
        this.keyword = keyword;
        return this;
    }

    /**
     * Utility method that instantiaties "Modifier"s for the keywords,
     * and puts them in a NodeList.
     */
    public static NodeList<Modifier> createModifierList(Modifier.Keyword... modifiers) {
        return Arrays.stream(modifiers).map(Modifier::new).collect(toNodeList());
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
    public Modifier clone() {
        return (Modifier) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModifierMetaModel getMetaModel() {
        return JavaParserMetaModel.modifierMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Modifier(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }
}
