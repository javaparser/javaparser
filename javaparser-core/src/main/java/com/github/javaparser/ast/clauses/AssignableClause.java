package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class AssignableClause extends Clause {
    @AllFieldsConstructor
    public AssignableClause(TokenRange tokenRange) {
        super(tokenRange);
    }
}
