package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.*;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typecheckingJmlTypes extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        useSystemSpecs = true; // Needed to be able to resolve b[] = x as a .put call
        super.setUp();
    }

    @Test public void testBigint() {
        helpTC(" class A { //@ ghost \\bigint b = 0; \n}");
    }

    @Test public void testReal() {
        helpTC(" class A { //@ ghost \\real b = 0; \n}");
    }

    @Test public void testTYPE() {
        helpTC(" class A { //@ ghost \\TYPE b ; \n}");
    }

    @Test public void testMinusBigint() {
        helpTC(" class A { //@ ghost \\bigint b = 0; ghost \\bigint bb = -b; \n}");
    }

    @Test public void testBinaryBigint() {
        helpTC(" class A { void m() { //@ ghost \\bigint b = 0; ghost \\bigint bb = b + b; set bb = b-b; set bb = b*b; set bb = b/b; \n}}");
    }

    @Test public void testArrayType() {
        helpTC(" class A { void m() { //@ ghost array<Object> b; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }

    @Test public void testIntsetType() {
        helpTC(" class A { void m() { //@ ghost intset b; ghost \\bigint i = 0; ghost boolean o = b[i];  set b[i] = true; \n}}");
    }

    @Test public void testIntmapType() {
        helpTC(" class A { void m() { //@ ghost intmap<Object> b ; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }

    @Test public void testSeqType() {
        helpTC(" class A { void m() { //@ ghost seq<Object> b ; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }

    @Test public void testMapType() {
        helpTC(" class A { void m() {  //@ ghost map<string,string> b ;   ghost string o ; set b[o] = o; ghost string bb = b[o]; \n}}");
    }

    @Test public void testMap2Type() {
        helpTC(" class A { void m() { //@ ghost map<Object,Object> b ;  ghost Object o = new Object(); set b[o] = o; ghost Object bb = b[o]; \n}}");
    }

    @Test public void testSetType() {
        helpTC(" class A { void m() {  //@ ghost set<Object> b ; ghost Object o = new Object(); set b[o] = true; ghost boolean bb = b[o]; \n}}");
    }

    @Test public void testStringType() {
        helpTC(" class A { void m() {  //@ ghost string b ; ghost char c = 'a'; set b[c] = 'b'; ghost char bb = b[c]; \n}}");
    }

    
    
}
