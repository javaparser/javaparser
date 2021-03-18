package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (3/17/21)
 */
public class JmlSpecification/*<T extends Node & Jmlish>*/ {
    private boolean singleLine;
    private Set<String> jmlTags;
    private NodeList<Node> elements;
}
