package com.github.javaparser;

/**
 * The range of tokens covered by this node.
 */
public class TokenRange {
    private final JavaToken begin;
    private final JavaToken end;
    
    public TokenRange(JavaToken begin, JavaToken end){
        this.begin = begin;
        this.end = end;
    }

    public JavaToken getBegin() {
        return begin;
    }

    public JavaToken getEnd() {
        return end;
    }
}
