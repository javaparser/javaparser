package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange;
import com.github.jmlparser.lint.LintProblem;

/**
 * @author Alexander Weigl
 * @version 1 (21.10.22)
 */
public record LintProblemMeta(String id, String message, String level) {

    public LintProblem create(NodeWithTokenRange<Node> n) {
        return new LintProblem(level(), message(), n.getTokenRange().orElse(null), null, id, ruleId);
    }
}
