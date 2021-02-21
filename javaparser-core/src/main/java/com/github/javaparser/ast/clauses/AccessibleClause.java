package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class AccessibleClause extends Clause {
    @AllFieldsConstructor
    public AccessibleClause(TokenRange tokenRange) {
        super(tokenRange);
    }
}
