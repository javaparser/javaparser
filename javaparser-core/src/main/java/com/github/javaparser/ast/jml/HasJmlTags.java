package com.github.javaparser.ast.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/21)
 */
public interface HasJmlTags<N extends Node> {
    N setJmlTags(NodeList<SimpleName> jmlTags);

    NodeList<SimpleName> getJmlTags();
}
