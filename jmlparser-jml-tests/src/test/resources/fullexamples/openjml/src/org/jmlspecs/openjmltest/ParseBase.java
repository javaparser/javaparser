package org.jmlspecs.openjmltest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.vistors.IJmlVisitor;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This class is the base class for test suites that just are exercising the parser,
 * without doing any further typechecking.  FOr this purpose the parser can be
 * called standalone, and the parse tree inspected. 
 * @author David Cok
 *
 */
abstract public class ParseBase extends JmlTestCase {

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath = "$A"+z+"$B";

    protected ParserFactory fac;
    protected ScannerFactory sfac;
    protected JmlParser parser;

    /** Set this to true in tests which start out the scanner in jml mode
     * (avoiding the need to begin the test string with a JML comment annotation)
     */
    protected boolean jml;

    @Override
    public void setUp() throws Exception {
        super.setUp();
        main.addOptions("compilePolicy","check");  // Don't do code generation
        main.addOptions("-specspath",   testspecpath);
        //main.register(context);
        JmlAttr.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        JmlEnter.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        sfac = ScannerFactory.instance(context);
        fac = ParserFactory.instance(context);
        print = false;
        jml = false;
    }

    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        fac = null;
        sfac = null;
    }

    /** Compiles the given string as the content of a compilation unit,
     * comparing the parse tree found to the expected node types and character
     * positions found in the second argument.
     * @param s the content of a compilation unit
     * @param list the expected parse tree formed by parsing the first argument
     * as a compilation unit, each node is represented by a node type (instance 
     * of Class) and character position (an int).
     */
    public void checkCompilationUnit(String s, Object ... list) {
        List<JCTree> out = parseCompilationUnit(s);
        checkParseTree(out,list);
    }

    // TODO - put in a few harness tests
    // TODO - test error messages
    public void checkCompilationUnitFailure(String failureMessage, String s, Object ... list) {
        boolean failed = false;
        try {
            checkCompilationUnit(s,list);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }
    
    /** Parses the content of a compilation unit, producing a list of nodes of
     * the parse tree
     * @param s the string to parse
     * @return the list of nodes in the resulting parse tree
     */
    public List<JCTree> parseCompilationUnit(String s) {
        Log.instance(context).useSource(new TestJavaFileObject(s));
        parser = ((JmlFactory)fac).newParser(s,false,true,true,jml);
        JCTree e = parser.parseCompilationUnit();
        return ParseTreeScanner.walk(e);
    }


    /** Compares a list of nodes to the expected values given in the 
     * second argument; the second argument is expected to consist of the
     * class of a node (e.g. JCIdent.class) and the preferred character 
     * position of that node, for each element of the actual list.  The two 
     * lists are compared (both for node type and position) and JUnit failures
     * are raised for the first difference found.
     * @param actual a list of nodes as produced by ParseTreeScanner.walk
     * @param expected a list of expected data - class types and character positions
     * for each node in turn
     */
    public void checkParseTree(List<JCTree> actual, Object[] expected) {
        try {
            int i = 0;
            int k = 0;
            if (print) {
                for (JCTree t: actual) {
                    System.out.println(t.getClass() + " " + t.getStartPosition() + " " + t.getPreferredPosition() + " " + parser.getEndPos(t));
                }
            }
            if (print) printDiagnostics();
            Object p1, p2, p3;
            for (JCTree t: actual) {
                if (i>=expected.length) break;
                assertEquals("Class not matched at token " + k, expected[i++], t.getClass());
                p1 = expected[i++];
                p2 = (i < expected.length && expected[i] instanceof Integer) ? expected[i++] : null;
                p3 = (i < expected.length && expected[i] instanceof Integer) ? expected[i++] : null;
                if (p3 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("Preferred position for token " + k, p2, t.getPreferredPosition());
                    assertEquals("End position for token " + k, p3, parser.getEndPos(t));
                } else if (p2 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("End position for token " + k, p2, parser.getEndPos(t));
                } else {
                    assertEquals("Preferred position for token " + k, p1, t.getPreferredPosition());
                }
                ++k;
            }
            if ( i != expected.length) fail("Incorrect number of nodes listed");
            if (parser.getScanner().token().kind != TokenKind.EOF) fail("Not at end of input");
        } catch (AssertionError e) {
            if (!print) printTree(actual);
            if (!print) printDiagnostics();
            throw e;
        }
    }
    
    /** Prints out the nodes of the tree */
    public void printTree(List<JCTree> list) {
        System.out.println("NODES FOR " + name.getMethodName());
        for (JCTree t: list) {
            System.out.println(t.getClass() + " " + t.getStartPosition() + " " + t.getPreferredPosition() + " " + parser.getEndPos(t));
        }
    }

    /** A tree visitor class that walks the tree (depth-first), 
     * creating a list of the nodes it encounters.
     */
    static public class ParseTreeScanner extends JmlTreeScanner implements IJmlVisitor {
        /** The list of nodes */
        private List<JCTree> list = new LinkedList<JCTree>();;

        /** Constructs the visitor, but otherwise does nothing. */
        public ParseTreeScanner() {
        }

        /** A convenience method to walk the given tree and return the list of
         * its nodes.
         * @param tree the tree to be walked
         * @return the list of nodes in depth-first traversal order
         */
        static public List<JCTree> walk(JCTree tree) {
            ParseTreeScanner t = new ParseTreeScanner();
            t.scan(tree);
            return t.result();
        }

        /** Returns a reference to the list accumulated so far.
         * @return the accumulator list
         */
        public List<JCTree> result() { return list; }

        /** Adds a node to the internal accumulator and then calls the
         * super class method.
         */
        @Override
        public void scan(JCTree t) {
            if (t == null) return;
            list.add(t);
            super.scan(t);
        }
    }


    /** Just to avoid Junit framework complaints about no tests */
    public void test() {} 
}
