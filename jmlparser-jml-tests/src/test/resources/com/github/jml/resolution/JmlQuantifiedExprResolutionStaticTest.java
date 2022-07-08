package com.github.jml.resolution;

/**
 * @author Alexander Weigl
 * @version 1 (08.07.22)
 */
public class JmlQuantifiedExprResolutionTest {
    int member;
    static int clazz = member;
    //@static invariant clazz != null; // should be ok.
    //@invariant clazz != null; // should be ok.
    //@static invariant member != null; // error

}

// e: z @ (line 10, column 18)
