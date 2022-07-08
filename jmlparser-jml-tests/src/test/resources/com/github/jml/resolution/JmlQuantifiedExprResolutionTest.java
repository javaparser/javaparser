package com.github.jml.resolution;

/**
 * @author Alexander Weigl
 * @version 1 (08.07.22)
 */
public class JmlQuantifiedExprResolutionTest {
    int z;
    //@invariant (\forall int x; x > 2; x > 5 * z);
    //@invariant (\exists int x; x > 2; x > 5 * z);
    //@invariant (\sum int x, int y; 0 < y < x < 25; x*y*z);
}
