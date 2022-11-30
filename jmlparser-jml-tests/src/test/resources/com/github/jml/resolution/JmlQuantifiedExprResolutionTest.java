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

//? type: x@(line 10,col 41)
//? type: x@(line 11,col 54)
//? name: x@(line 10,col 34) to x@(line 10,col 27)
//? type: z@(line 9,col 49)
//? type: x@(line 11,col 46)
//? name: x@(line 11,col 46) to x@(line 11,col 24)
//? type: z@(line 10,col 49)
//? name: z@(line 9,col 49) to z@(line 8,col 5)
//? name: y@(line 11,col 56) to y@(line 11,col 31)
//? name: x@(line 9,col 41) to x@(line 9,col 27)
//? type: x@(line 10,col 34)
//? name: x@(line 10,col 41) to x@(line 10,col 27)
//? name: z@(line 10,col 49) to z@(line 8,col 5)
//? name: x@(line 11,col 54) to x@(line 11,col 24)
//? type: x@(line 9,col 34)
//? type: y@(line 11,col 42)
//? type: z@(line 11,col 58)
//? name: x@(line 9,col 34) to x@(line 9,col 27)
//? type: x@(line 9,col 41)
//? name: y@(line 11,col 42) to y@(line 11,col 31)
//? type: y@(line 11,col 56)
//? name: z@(line 11,col 58) to z@(line 8,col 5)
