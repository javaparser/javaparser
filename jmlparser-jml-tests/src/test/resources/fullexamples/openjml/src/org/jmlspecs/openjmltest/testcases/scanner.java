package org.jmlspecs.openjmltest.testcases;

import static com.sun.tools.javac.parser.Tokens.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.JmlTokenKind.*;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjmltest.JmlTestCase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.junit.Ignore;
import org.junit.Test;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Tokens;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

import static org.junit.Assert.*;

import java.util.Locale;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

// TODO - should test unicode, especially with multiple backslashes
// TODO - should test errPos for error tokens (is endPos set?)

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class scanner extends JmlTestCase {

    final static JmlTokenKind EJML = ENDJMLCOMMENT;
    
    ScannerFactory fac;
    
    String[] keys;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh scanner factory for each test */
    @Override
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        fac = ScannerFactory.instance(context);
        keys = null;
    }

    /** This is a helper routine to check tests that are supposed to issue
     * JUnit test failures.
     * 
     * @param failureMessage The expected JUnit failure message
     * @param s The string to parse
     * @param list The tokens expected
     * @param positions The expected start and end positions for each token
     * @param numErrors The expected number of scanning errors
     */
    //@ requires positions != null && list != null ==> positions.length == list.length*2;
    public void helpFailure(String failureMessage, String s, ITokenKind[] list, /*@nullable*/ int[] positions, int numErrors) {
        boolean failed = false;
        try {
            helpScanner(s,list,positions,numErrors);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test harness failed to report an error");
    }


    /** This scans the input string and checks whether the tokens obtained
     * match those in the list array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is 0.  The positions array contains a start and end position
     * for each token.
     */
    public void helpScanner(String s, ITokenKind[] list, int[] positions) {
        helpScanner(s,list,positions,0);
    }
    
    /** This scans the input string and checks whether the tokens obtained
     * match those in the list array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is the last argument.  The positions array contains a start and end position
     * for each token.
     */
    public void helpScanner(String s, ITokenKind[] list, int[] positions, int numErrors) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(s) );
            JmlScanner sc = (JmlScanner)fac.newScanner(s, true);
            if (keys != null) {
                for (String k: keys) { ((JmlScanner)sc).keys().add(k); }
            }
            int i = 0;
            while (i<list.length) {
                sc.nextToken();
                if (print) System.out.println(sc.token() + " " + ((JmlScanner)sc).jmlToken());
                Token e = sc.token();
                if (e.ikind != list[i]) {
                    fail("Unexpected token at position " + i + " expected: " + list[i] + " actual: " + e.kind );
                }
                if (positions != null && 2*i+1 < positions.length) {
                    assertEquals("pos for token " + i, positions[2*i], e.pos);
                    assertEquals("endpos for token " + i, positions[2*i+1], e.endPos);
                }
                i++;
            }
            sc.nextToken();
            if (sc.token().kind != TokenKind.EOF) {
                fail("Scanner not at EOF: " + sc.token().kind);
            }
            if (collector.getDiagnostics().size() != numErrors) {
                if (!noExtraPrinting) printDiagnostics();
                fail("Saw wrong number of errors: expected " + numErrors 
                        + " actual " + collector.getDiagnostics().size());
            }
            if (positions != null && 2*i != positions.length) fail("Number of start/end locations (" + (positions.length) + ") should be double the number of tokens (" + i + ")");
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
    ////////////////////////////////////////////////////////////////////////
    
    /** Test scanning something very simple */
    @Test public void testSomeJava() {
        helpScanner("",new TokenKind[]{},null);
        helpScanner("A",new TokenKind[]{IDENTIFIER},new int[]{0,1});
    }
    
    /** Test some unicode */
    @Test public void testSomeUnicode() {
        helpScanner("\\u0041\\u0020\\u0041",  // A space A
                new TokenKind[]{IDENTIFIER,IDENTIFIER},
                new int[]{5,11,17,18});  // Current behavior but wrong - BUG - FIXME
                //new int[]{0,6,12,18}); // This is what it should be
    }
    
    /** Test some unicode  - multiple u*/
    @Test public void testSomeUnicode2() {
        helpScanner("\\uuuu0041 A",
                new TokenKind[]{IDENTIFIER,IDENTIFIER},
                null);  
    }

    // FIXME - Java tokenizer recovery from bad character is not robust
    /** Test some unicode  - first backslash is an error and ignored */
    @Test public void testSomeUnicode3() {
        helpScanner(
                "\\\\u0041 A",
                new ITokenKind[]{ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{0,6,6,7,8,9},
                1);
                checkMessages("/TEST.java:1: illegal character: '\\'",1);  
    }
    
    /** This tests that the test harness records if not enough tokens are listed */
    @Test public void testHarness1() {
        helpFailure("Scanner not at EOF: token.identifier",
                "A A",new ITokenKind[]{IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness2() {
        helpFailure("Unexpected token at position 1 expected: token.identifier actual: token.end-of-input",
                "A",new ITokenKind[]{IDENTIFIER,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if a wrong token is listed */
    @Test public void testHarness3() {
        helpFailure("Unexpected token at position 0 expected: public actual: token.identifier",
                "A",new ITokenKind[]{PUBLIC},null,0);
    }

    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness4() {
        helpFailure("Unexpected token at position 2 expected: token.identifier actual: token.end-of-input",
                "A",new ITokenKind[]{IDENTIFIER,EOF,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if wrong start position is given */
    @Test public void testHarness5() {
        helpFailure("pos for token 0 expected:<1> but was:<0>",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{1,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong end position is given */
    @Test public void testHarness6() {
        helpFailure("endpos for token 0 expected:<2> but was:<1>",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{0,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong number of errors is given */
    @Test public void testHarness7() {
        noExtraPrinting = true;
        helpFailure("Saw wrong number of errors: expected 1 actual 0",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{0,1,1,1},1);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness8() {
        helpFailure("Number of start/end locations (1) should be double the number of tokens (2)",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{0},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness9() {
        helpFailure("Number of start/end locations (2) should be double the number of tokens (2)",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{0,1},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness10() {
        helpFailure("Number of start/end locations (0) should be double the number of tokens (2)",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{},0);
    }
    
    /** This tests that the test harness fails if too many positions are given */
    @Test public void testHarness11() {
        helpFailure("Number of start/end locations (7) should be double the number of tokens (2)",
                "A",new ITokenKind[]{IDENTIFIER,EOF},new int[]{0,1,1,1,4,5,6},0);
    }
    

    /** Tests that JML keywords are not found in Java */
    @Test public void testJmlKeywordsNotInJml() {
        helpScanner("requires ensures pure",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{0,8,9,16,17,21});
    }
    
    
    /** Tests JML operators */
    @Test public void testOperators() {
        helpScanner("/*@ ==> <== <: <==> <=!=> <- */",
                new ITokenKind[]{IMPLIES,REVERSE_IMPLIES,SUBTYPE_OF,EQUIVALENCE,INEQUIVALENCE,LEFT_ARROW,EJML},
                new int[]{4,7, 8,11, 12,14, 15,19, 20,25, 26,28, 29,31});
    }
    
    /** Tests the Java operators related to JML operators */
    @Test public void testOperators1() {
        helpScanner("/*@ ==  <=  <  */",
                new ITokenKind[]{EQEQ,LTEQ,LT,EJML},
                new int[]{4,6,8,10,12,13,15,17});
    }
    
    /** Tests JML operators when in Java land */
    @Test public void testOperators2() {
        helpScanner("    ==> <== <: <==> <=!=> ",
                new ITokenKind[]{EQEQ,GT, LTEQ,EQ, LT,COLON, LTEQ,EQ,GT, LTEQ,BANGEQ,GT},
                new int[]{4,6,6,7, 8,10,10,11, 12,13,13,14, 15,17,17,18,18,19, 20,22,22,24,24,25});
    }
    
    @Test public void testOperators3() {
        helpScanner("/*@ <<< <<<= <: <:= @ */",
                new ITokenKind[]{WF_LT,WF_LE,SUBTYPE_OF,SUBTYPE_OF_EQ, MONKEYS_AT,EJML},
                new int[]{4,7, 8,12, 13,15, 16,19, 20,21, 22,24});
    }
    @Test public void testBadOperator() {
        helpScanner("/*@ <=! + */",
                new ITokenKind[]{LTEQ,BANG,PLUS,EJML},
                new int[]{4,6,6,7,8,9,10,12});
    }

    @Test public void testBadOperator2() {
        helpScanner("/*@ <=!= + */",
                new ITokenKind[]{LTEQ,BANGEQ,PLUS,EJML},
                new int[]{4,6,6,8,9,10,11,13});
    }

    @Test public void testArrow() {  // Now a Java operator, but in JML context
        helpScanner("/*@ -> */",
                new ITokenKind[]{ARROW,EJML},
                new int[]{4,6,7,9});
    }

    @Test public void testArrow2() {  // Now a Java operator, in Java context
        helpScanner("    ->   ",
                new ITokenKind[]{ARROW},
                new int[]{4,6});
    }

    // NOTE:  In the test strings, backslash characters must be escaped.  So
    // within the string you write \\result, not \result, to get the effect of
    // \result in a test program.
    
    /** Test that a backslash token is found */
    @Test public void testBackslash() {
        helpScanner("/*@ \\result */",
                new ITokenKind[]{IDENTIFIER,EJML},
                null);
    }
    
    /** Test that two immediately consecutive backslash tokens are found */
    @Test public void testBackslash1() {
        helpScanner("/*@ \\result\\result */",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML},
                null);
    }
    
    /** Test that backslash tokens are found immediately after a line termination */
    @Test public void testBackslash2() {
        helpScanner("/*@ \\result \n\\result*/",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML},
                null);
    }
    
    /** Test that a backslash token without the backslash is a regular identifier */
    @Test public void testBackslash3() {
        helpScanner("/*@ \\result result*/",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML},
                null);
    }
    
    /** Test for an invalid backslash identifier */
    @Test public void testBackslash5() {
        helpScanner("/*@ \\xyz result*/",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML},
                null,
                0);
        checkMessages();
    }

    /** Test for a JML backslash with no identifier */
    @Test public void testBackslash6() {
        helpScanner("/*@ \\ \\result*/",
                new ITokenKind[]{ERROR,IDENTIFIER,EJML},
                null,
                1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    

    /** Test an empty Java line comment */
    @Test public void testEmptyJavaComment() {
        helpScanner("//",
                new ITokenKind[]{},
                new int[]{});
    }

    /** Test a mismatched comment ending */
    @Test public void testMisMatchedJMLComment() {
        helpScanner("//@*/ requires",
                new ITokenKind[]{STAR,SLASH,IDENTIFIER,EOF},
                null);
    }

    /** Test an empty line comment */
    @Test public void testEmptyComment() {
        helpScanner("//\n//@requires",
                new ITokenKind[]{IDENTIFIER,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment() {
        helpScanner("//@requires //@ requires",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment3() {
        helpScanner("/*@requires /*@ requires */ public   */ public",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML,PUBLIC,STAR,SLASH,PUBLIC,EOF},
                new int[] {3,11,16,24,25,27,28,34,37,38,38,39,40,46,46,46});
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment4() {
        helpScanner("/*@requires //@ requires  \n requires */ public",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,IDENTIFIER,EJML,PUBLIC,EOF},
                new int[] {3,11,16,24,28,36,37,39,40,46,46,46});
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment2() {
        helpScanner("/*@requires //@ requires */ public",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML,PUBLIC,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment5() {
        helpScanner("//@requires /*@ requires\n public   */ public  ",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML,PUBLIC,STAR, SLASH,PUBLIC,EOF},
                null);
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment() {
        helpScanner("//@requires // requires",
                new ITokenKind[]{IDENTIFIER,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJavaComment2() {
        helpScanner("//@requires /* requires */ ensures ",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EOF},
                new int[] {3,11,27,34,34,34});
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJavaComment3() { 
        helpScanner("//@requires /* requires ensures \n signals */ modifies ",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EOF},
                new int[]{3,11,45,53,53,53},
                1);
        checkMessages("/TEST.java:1: Java block comment must terminate within the JML line comment",13);
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment4() {
        helpScanner("/*@requires // modifies \n ensures */ signals ",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML,IDENTIFIER,EOF},
                new int[]{3,11,26,33,34,36,37,44,44,44}); // FIXME - check position of EOF
    }

    /** Test an embedded Java comment (which ends a JML block comment) */
    @Test public void testEmbeddedJavaComment6() {
        helpScanner("/*@requires /* modifies \n ensures */ ensures */ signals ",
                new ITokenKind[]{IDENTIFIER,EJML,IDENTIFIER,STAR,SLASH,IDENTIFIER,EOF},
                new int[]{3,11,34,36,37,44,45,46,46,47,48,55,55,55});
    }

    @Test public void testLineComment1() {
        helpScanner("//@ requires",new ITokenKind[]{IDENTIFIER,EOF},null);
    }

    // NOTE: The scanner absorbs ending whitespace into the EOF.
    @Test public void testLineComment2() {
        helpScanner("//@ requires\n",new ITokenKind[]{IDENTIFIER,EOF},null);
    }

    /** Test that a line comment ends with a NL character */
    @Test public void testLineComment3() {
        helpScanner("//@ requires\n ",
                new ITokenKind[]{IDENTIFIER,EJML},
                new int[]{4,12,12,13});
    }

    /** Test that a line comment ends with a CR character */
    @Test public void testLineComment4() {
        helpScanner("//@ requires\r ",
                new ITokenKind[]{IDENTIFIER,EJML},
                null);
    }

    /** Test that a line comment ends with a CR NL combination */
    @Test public void testLineComment5() {
        helpScanner("//@ requires\r\n",
                new ITokenKind[]{IDENTIFIER,EJML},
                null);
    }

    /** Test that JML identifiers are not found after a JML line comment ends*/
    @Test public void testLineComment6() {
        helpScanner("//@ requires\nrequires",
                new ITokenKind[]{IDENTIFIER,EJML,IDENTIFIER},
                null);
    }
    
    /** Test that an @ at the end of a line comment is found */
    @Test public void testLineComment7() {
        helpScanner("//@ requires @\n ",
                new ITokenKind[]{IDENTIFIER,MONKEYS_AT,EJML},
                null);
    }
    
    /** Test an empty line comment */
    @Test public void testLineComment8() {
        helpScanner("//\nrequires ",
                new ITokenKind[]{IDENTIFIER},
                null);
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment9() {
        helpScanner("//@\nrequires ",
                new ITokenKind[]{IDENTIFIER},
                null);
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment10() {
        helpScanner("//@@@@@\nrequires ",
                new ITokenKind[]{IDENTIFIER},
                null);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11() {
        helpScanner("//@@x\\@@@\nrequires ",
                new ITokenKind[]{IDENTIFIER,ERROR,MONKEYS_AT,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",6);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11a() {
        helpScanner("//@@\\@x@@\nrequires ",
                new ITokenKind[]{ERROR,MONKEYS_AT,IDENTIFIER,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    
//    @Test public void testMultiLine() {
//        helpScanner("/*@ requires\nrequires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }
//
//    @Test public void testMultiLine1() {
//        helpScanner("/*@ requires\n  requires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }
//
//    @Test public void testMultiLine2() {
//        helpScanner("/*@ requires\n@requires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }
//
//    @Test public void testMultiLine3() {
//        helpScanner("/*@ requires\n@@@requires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }
//
//    @Test public void testMultiLine4() {
//        helpScanner("/*@ requires\n @requires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }
//
//    @Test public void testMultiLine5() {
//        helpScanner("/*@ requires\n  @@@requires@*/",
//                new ITokenKind[]{REQUIRES,REQUIRES,EJML},
//                null);
//    }

    @Test public void testMultiLineError() {
        helpScanner("/*@ \\result\n  @@@\\xyz@*/",
                new ITokenKind[]{IDENTIFIER,IDENTIFIER,EJML,EOF},
                new int[]{4,11,17,21,21,24,24,24},
                0);
        checkMessages();
    }

    @Test public void testInformalComment() {
        helpScanner("/*@ \\result(* requires *)*/",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,25,25,27},
                0);
    }
    @Test public void testInformalComment2() {
        helpScanner("/*@ \\result(* requires *****)*/",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,29,29,31},
                0);
    }
    @Test public void testInformalComment3() {
        helpScanner("/*@ \\result(* requires **** *)*/",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,30,30,32},
                0);
    }
    

    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4() {
        helpScanner("/*@ \\result(* requires **** */",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,28,28,30},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4a() {
        helpScanner("/*@ \\result(* requires *\n*** */",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,29,29,31},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4b() {
        helpScanner("/*@ \\result(* requires *\n*** ",
                new ITokenKind[]{ERROR,EOF},
                null, //new int[]{4,11,11,30,30,31},
                1);
        checkMessages("/TEST.java:1: unclosed comment",1);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5() {
        helpScanner("//@ \\result(* requires **** \n public",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EJML,PUBLIC,EOF},
                new int[]{4,11,11,28,28,29,30,36,36,36},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5a() {
        helpScanner("//@ \\result(* requires *****",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,EOF},
                new int[]{4,11,11,28,28,28},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment6() {
        helpScanner("//@ \\result(* requires ***\"*) \" requires\n",
                new ITokenKind[]{IDENTIFIER,INFORMAL_COMMENT,ERROR,EOF},
                new int[]{4,11,11,29,30,40,40,40},  // FIXME - check posiiton of EOF
                1);
        checkMessages("/TEST.java:1: unclosed string literal",31);
    }
    
    @Test public void testStringLiteral() {
        Scanner sc = fac.newScanner("\"\\tA\\\\B\"", true);
        sc.nextToken();
        assertEquals(STRINGLITERAL,sc.token().kind);
        assertEquals("\tA\\B",sc.token().stringVal());
    }
    
    @Test public void testCharLiteral() {
        Scanner sc = fac.newScanner("\'\\t\'", true);
        sc.nextToken();
        assertEquals(CHARLITERAL,sc.token().kind);
        assertEquals("\t",sc.token().stringVal());
    }
    
    @Test public void testIntLiteralWithUnderscore() {
        String v = "123_456";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("123456",sc.token().stringVal());
        assertEquals(123456,Integer.parseInt(sc.token().stringVal()));
    }
    
    @Test public void testIntLiteralWithUnderscoreBin() {
        String v = "0b0101_1010";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("01011010",sc.token().stringVal());
        assertEquals(90,Integer.parseInt(sc.token().stringVal(),2));
    }
    
    @Test public void testIntLiteralWithUnderscoreHex() {
        String v = "0xDE_AF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("DEAF",sc.token().stringVal());
        assertEquals(57007,Integer.parseInt(sc.token().stringVal(),16));
    }
    
    @Test public void testIntLiteralWithUnderscoreHexLong() {
        String v = "0xDEAF_DEAF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("DEAFDEAF",sc.token().stringVal());
        assertEquals(3736067759L,Long.parseLong(sc.token().stringVal(),16));
    }
    
    @Test public void testDotDot() {
        helpScanner("//@..",
                new ITokenKind[]{DOT_DOT,EOF},
                new int[]{3,5,5,5},
                0);
    }
    
//    @Test public void testDotDot2() {
//        helpScanner("//@ modifies ..;",
//                new ITokenKind[]{ASSIGNABLE,DOT_DOT,SEMI,EOF},
//                null,
//                0);
//    }
    
    @Test public void testDotDot2a() {
        helpScanner("//@ 123..456;",
                new ITokenKind[]{INTLITERAL,DOT_DOT,INTLITERAL,SEMI,EOF},
                null,
                0);
    }
    
//    @Test public void testDotDot3() {
//        helpScanner("//@ modifies a[b .. c];",
//                new ITokenKind[]{ASSIGNABLE,IDENTIFIER,LBRACKET,IDENTIFIER,DOT_DOT,IDENTIFIER,RBRACKET,SEMI,EOF},
//                null,
//                0);
//    }
// 
//    @Test public void testDotDot4() {
//        helpScanner("//@ modifies a[0..4];",
//                new ITokenKind[]{ASSIGNABLE,IDENTIFIER,LBRACKET,INTLITERAL,DOT_DOT,INTLITERAL,RBRACKET,SEMI,EOF},
//                null,
//                0);
//    }
// 
//    @Test public void testDotDot4a() {
//        helpScanner("//@ modifies a[0 ..4];",
//                new ITokenKind[]{ASSIGNABLE,IDENTIFIER,LBRACKET,INTLITERAL,DOT_DOT,INTLITERAL,RBRACKET,SEMI,EOF},
//                null,
//                0);
//    }
// 
//    @Test public void testDotDot5() {
//        helpScanner("//@ modifies ..234;",
//                new ITokenKind[]{ASSIGNABLE,DOT_DOT,INTLITERAL,SEMI,EOF},
//                null,
//                0);
//    }
//    
//    @Test public void testDotDot6() {
//        helpScanner("//@ modifies .234;",
//                new ITokenKind[]{ASSIGNABLE,DOUBLELITERAL,SEMI,EOF},
//                null,
//                0);
//    }
//    
//    @Test public void testDotDot7() {
//        helpScanner("//@ modifies 0.234;",
//                new ITokenKind[]{ASSIGNABLE,DOUBLELITERAL,SEMI,EOF},
//                null,
//                0);
//    }
//    
//    @Test public void testDotDot8() {
//        helpScanner("//@ modifies a[0. .4];",
//                new ITokenKind[]{ASSIGNABLE,IDENTIFIER,LBRACKET,DOUBLELITERAL,DOUBLELITERAL,RBRACKET,SEMI,EOF},
//                null,
//                0);
//    }
 
    @Test public void testDotDot9() {
        helpScanner("//@ 0xApA\n ",
                new ITokenKind[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot10() {
        helpScanner("//@ 1.0eZ \n ",
                new ITokenKind[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot11() {
        helpScanner("//@ 0xA.0pZ\n ",
                new ITokenKind[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot12() {
        helpScanner("//@ 0xA.Z\n ",
                new ITokenKind[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testConditionalKey1() {
        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
                new ITokenKind[]{EOF},
                null);
    }

//    @Test public void testConditionalKey2() {
//        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
//                new ITokenKind[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
//                null);
//    }
//
//    @Test public void testConditionalKey3() {
//        keys = new String[]{"POS"};
//        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
//                new ITokenKind[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
//                null);
//    }

    @Test public void testConditionalKey4() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
                new ITokenKind[]{EOF},
                null);
    }

    @Test public void testConditionalKey5() {
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new ITokenKind[]{EOF},
                null);
    }

//    @Test public void testConditionalKey6() {
//        keys = new String[]{"POS"};
//        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
//                new ITokenKind[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
//                null);
//    }
//
    @Test public void testConditionalKey7() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new ITokenKind[]{EOF},
                null);
    }

    @Test public void testConditionalKey8() {
        keys = new String[]{"NEG","POS"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new ITokenKind[]{EOF},
                null);
    }

//    @Test public void testConditionalKey9() {
//    	Options.instance(context).put("-Xlint:deprecation","true");
//        helpScanner("//+@ requires\n  /*+@ requires */",
//                new ITokenKind[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
//                null,2);
//        checkMessages("/TEST.java:1: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",3
//        		,"/TEST.java:2: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",5);
//    }

    @Test public void testConditionalKey10() {
    	Options.instance(context).put("-Xlint:deprecation","true");
        helpScanner("//-@ requires\n  /*-@ requires */",
                new ITokenKind[]{EOF},
                null,
                2);
        checkMessages("/TEST.java:1: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",3
        		,"/TEST.java:2: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",5);
    }

//    @Test public void testConditionalKey9d() {
//        helpScanner("//+@ requires\n  /*+@ requires */",
//                new ITokenKind[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
//                null,0);
//    }

    @Test public void testConditionalKey10d() {
        helpScanner("//-@ requires\n  /*-@ requires */",
                new ITokenKind[]{EOF},
                null,
                0);
    }



}
