package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.SwitchEntryStmt;

import java.util.Optional;

/**
 * The common interface of {@link com.github.javaparser.ast.expr.SwitchExpr} and {@link com.github.javaparser.ast.stmt.SwitchStmt}
 */
public interface SwitchNode {
    NodeList<SwitchEntryStmt> getEntries();

    SwitchEntryStmt getEntry(int i);

    Expression getSelector();

    SwitchNode setEntries(NodeList<SwitchEntryStmt> entries);

    SwitchNode setSelector(Expression selector);

    boolean remove(Node node);

    SwitchNode clone();

    boolean replace(Node node, Node replacementNode);

    Optional<Comment> getComment();
    
    // Too bad Node isn't an interface, or this could have easily inherited all of its methods.
    // Add more when required.
}
