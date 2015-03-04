package com.github.javaparser.ast.lexical;

import com.github.javaparser.Position;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public abstract class Lexeme {

    private Lexeme previous;
    private Lexeme next;
    private Position begin;
    private Position end;

    public Lexeme() {
    }

    public abstract LexemeKind getLexemeKind();

    public boolean is(LexemeKind first, LexemeKind... rest) {
        return EnumSet.of(first, rest).contains(getLexemeKind());
    }

    public boolean is(CommentKind first, CommentKind... rest) {
        return false;
    }

    public boolean is(KeywordKind first, KeywordKind... rest) {
        return false;
    }

    public boolean is(LiteralKind first, LiteralKind... rest) {
        return false;
    }

    public boolean is(OperatorKind first, OperatorKind... rest) {
        return false;
    }

    public boolean is(SeparatorKind first, SeparatorKind... rest) {
        return false;
    }

    public boolean is(WhitespaceKind first, WhitespaceKind... rest) {
        return false;
    }

    public abstract String image();

    public Position begin() {
        return begin;
    }

    public Position end() {
        return end;
    }

    public Lexeme previous() {
        return (Lexeme) previous;
    }

    public Lexeme next() {
        return (Lexeme) next;
    }

    public void setPrevious(Lexeme previous) {
        this.previous = previous;
    }

    public void setNext(Lexeme next) {
        this.next = next;
    }

    public void setBegin(Position begin) {
        this.begin = begin;
    }

    public void setEnd(Position end) {
        this.end = end;
    }
}
