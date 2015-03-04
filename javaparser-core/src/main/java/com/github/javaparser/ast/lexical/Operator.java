package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Operator extends Lexeme {

    private final OperatorKind kind;

    public Operator(OperatorKind kind) {
        super();
        this.kind = kind;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.OPERATOR;
    }

    public OperatorKind getOperatorKind() {
        return kind;
    }

    @Override
    public boolean is(OperatorKind first, OperatorKind... rest) {
        return EnumSet.of(first, rest).contains(getOperatorKind());
    }

    @Override
    public String image() {
        return kind.image;
    }
}
