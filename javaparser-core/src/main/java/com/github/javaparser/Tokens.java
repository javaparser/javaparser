package com.github.javaparser;

import static com.github.javaparser.utils.Utils.assertNotNull;

public class Tokens {
    public final JavaToken begin;
    public final JavaToken end;

    public Tokens(JavaToken begin, JavaToken end) {
        assertNotNull(begin);
        assertNotNull(end);
        this.begin = begin;
        this.end = end;
    }
}
