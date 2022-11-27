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

//? name: clazz@(line 10,col 25) to clazz@(line 9,col 5)
//? name: clazz@(line 11,col 18) to clazz@(line 9,col 5)
//? name: member@(line 12,col 25) to member@(line 8,col 5)
//? name: member@(line 9,col 24) to member@(line 8,col 5)
//? type: clazz@(line 10,col 25)
//? type: clazz@(line 11,col 18)
//? type: member@(line 9,col 24)
//? name: clazz@(line 10,col 25) to clazz@(line 9,col 5)
//? name: clazz@(line 11,col 18) to clazz@(line 9,col 5)
//? name: member@(line 12,col 25) to member@(line 8,col 5)
//? name: member@(line 9,col 24) to member@(line 8,col 5)
//? type: clazz@(line 10,col 25)
//? type: clazz@(line 11,col 18)
//? type: member@(line 12,col 25)
//? type: member@(line 9,col 24)
