package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;

/**
 * @author Alexander Weigl
 * @version 1 (11/23/21)
 */
public class JmlDocModifier extends Modifier {
    private final NodeList<JmlDoc> jmlComments;

    @AllFieldsConstructor
    public JmlDocModifier(NodeList<JmlDoc> jmlComments) {
        this.jmlComments = jmlComments;
    }
}
