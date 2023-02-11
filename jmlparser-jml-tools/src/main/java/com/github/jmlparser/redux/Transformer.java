package com.github.jmlparser.redux;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.ForEachStmt;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public interface Transformer {
    Node apply(Node a);

}
