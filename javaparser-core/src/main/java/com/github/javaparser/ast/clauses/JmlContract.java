package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.stmt.Behavior;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (3/14/21)
 */
public class JmlContract extends Node implements Jmlish {
    private Behavior behavior;
    private Modifier modifier;
    private final NodeList<JmlClause> clauses = new NodeList<>();
    private final NodeList<JmlContract> subContracts = new NodeList<>();

    public JmlContract() {
        super(null);
    }

    @AllFieldsConstructor
    public JmlContract(
            Behavior behavior, Modifier modifier, NodeList<JmlClause> clauses,
            NodeList<JmlContract> subContracts) {
        super(null);

    }


    public JmlContract(TokenRange tokenRange) {
        super(tokenRange);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
