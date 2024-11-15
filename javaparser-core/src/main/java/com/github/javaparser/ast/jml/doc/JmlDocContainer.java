package com.github.javaparser.ast.jml.doc;

import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.NodeList;

/**
 * @author Alexander Weigl
 * @version 1 (26.05.22)
 */
public  interface JmlDocContainer {

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    NodeList<JmlDoc> getJmlComments();
}
