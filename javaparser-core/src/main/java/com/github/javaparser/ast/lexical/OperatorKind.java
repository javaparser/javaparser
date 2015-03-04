package com.github.javaparser.ast.lexical;

/**
* @author Didier Villevalois
*/
public enum OperatorKind {
    ASSIGN("="),
    LT("<"),
    BANG("!"),
    TILDE("~"),
    HOOK("?"),
    COLON(":"),
    EQ("=="),
    LE("<="),
    GE(">="),
    NE("!="),
    SC_OR("||"),
    SC_AND("&&"),
    INCR("++"),
    DECR("--"),
    PLUS("+"),
    MINUS("-"),
    STAR("*"),
    SLASH("/"),
    BIT_AND("&"),
    BIT_OR("|"),
    XOR("^"),
    REM("%"),
    LSHIFT("<<"),
    PLUSASSIGN("+="),
    MINUSASSIGN("-="),
    STARASSIGN("*="),
    SLASHASSIGN("/="),
    ANDASSIGN("&="),
    ORASSIGN("|="),
    XORASSIGN("^="),
    REMASSIGN("%="),
    LSHIFTASSIGN("<<="),
    RSIGNEDSHIFTASSIGN(">>="),
    RUNSIGNEDSHIFTASSIGN(">>>="),
    ELLIPSIS("..."),
    ARROW("->"),
    DOUBLECOLON("::"),
    RUNSIGNEDSHIFT(">>>"),
    RSIGNEDSHIFT(">>"),
    GT(">"),
    // Keep the last comma
    ;

    public final String image;

    OperatorKind(String image) {
        this.image = image;
    }
}
