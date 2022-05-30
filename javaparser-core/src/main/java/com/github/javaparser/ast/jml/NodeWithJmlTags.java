package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.22)
 */
public interface NodeWithJmlTags<R extends Node> {
    NodeList<SimpleName> getJmlTags();
    R setJmlTags(NodeList<SimpleName> tags);
}
