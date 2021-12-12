package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocModifier implements Modifier.Keyword {
    private final NodeList<JmlDoc> jmlComments;

    @AllFieldsConstructor
    public JmlDocModifier(NodeList<JmlDoc> jmlComments) {
        this.jmlComments = jmlComments;
    }

    @Override
    public String asString() {
        return "[[JML modifiers]]";
    }

    @Override
    public String name() {
        return asString();
    }
}
