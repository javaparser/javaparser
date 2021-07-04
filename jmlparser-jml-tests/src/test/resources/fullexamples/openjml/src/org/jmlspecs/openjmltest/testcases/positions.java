package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Arrays;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjmltest.JmlTestCase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Log;

// This test class checks that the parser produces correct positions for the various parsed 
// constructs. Each one should have a start position, end position, and a preferred position.
// The first two should span the construct from beginning to end. Note that the end position is
// one beyond the textual end; also these are character positions from the beginning of the file,
// with 0 being the first character. The 'preferred position' is the location to use when a single
// character is wanted. It is often the same as the start position, but in some case not; for example,
// for a binary operation, the preferred position is the location of the operator.

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class positions extends JmlTestCase {

    @Rule public TestName testname = new TestName();

    ParserFactory parserFactory;
    
    Test test;
    
    /** Initializes a fresh parser for each test */
    @Override
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        parserFactory = ParserFactory.instance(context);
    }

    @Parameters
    static public java.util.Collection<Object[]> datax() {
        return Arrays.asList(tests);
    }
    
    public positions(Test test) {
        this.test = test;
    }
    
    public static class Print extends JmlTreeScanner {
        
        
        public Print() {
        }
        
        public void scan(JCTree tree) {
            if(tree!=null) {
                System.out.println(tree.getClass());
                tree.accept(this);
            }
        }
        
        static void print(JCTree tree) {
            tree.accept(new Print());
        }

    }

    public static class Finder extends JmlTreeScanner {
        
        Class<?> clazz;
        JCTree done = null;
        
        public Finder(Class<?> clazz) {
            this.clazz = clazz;
        }
        
        public void scan(JCTree tree) {
            if (done != null) return;
            if (tree == null) return;
            if (tree.getClass() == clazz) { done = tree; return; }
            if(tree!=null) tree.accept(this);
        }
        
        static JCTree find(Class<?> clazz, JCTree tree) {
            Finder f = new Finder(clazz);
            tree.accept(f);
            return f.done;
        }

    }

    public void helpParser(boolean compunit, String markedString, Class<?> clazz, int numErrors) {
        try {
            int startpos = markedString.indexOf('#');
            int prefpos = markedString.indexOf('#',startpos+1)-1;
            int endpos = markedString.indexOf('#',prefpos+2)-2;
            String testString = markedString.replaceAll("#","");
            Log log = Log.instance(context);
            log.useSource(new TestJavaFileObject(testString) );
            JmlParser parser = (JmlParser)parserFactory.newParser(testString, false, true, true);
            JCTree result;
            JCTree ztree = null;
            try {
            if (compunit) {
                JCCompilationUnit tree = parser.parseCompilationUnit();
                ztree = tree;
                assertTrue("parse failure", tree != null);
                result = Finder.find(clazz,tree);
                if (collector.getDiagnostics().size() != numErrors) {
                    printDiagnostics();
                    fail("Saw errors: expected " + numErrors 
                                            + " actual " + collector.getDiagnostics().size());
                }
                assertTrue("failed to find node", result != null);
                assertEquals("start position-A", startpos, result.getStartPosition());
                assertEquals("start position-B", startpos, parser.getStartPos(result));
                assertEquals("pref position", prefpos, result.getPreferredPosition());
                assertEquals("end position-A", endpos, result.getEndPosition(tree.endPositions));
                assertEquals("end position-B", endpos, parser.getEndPos(result));
            } else {
                parser.getScanner().setJml(true);
                JCExpression tree = parser.parseExpression();
                ztree = tree;
                result = Finder.find(clazz,tree);
                if (collector.getDiagnostics().size() != numErrors) {
                    printDiagnostics();
                    fail("Saw errors: expected " + numErrors 
                                            + " actual " + collector.getDiagnostics().size());
                }
                assertTrue("failed to find node", result != null);
                assertEquals("start position-A", startpos, result.getStartPosition());
                assertEquals("start position-B", startpos, parser.getStartPos(result));
                assertEquals("pref position", prefpos, result.getPreferredPosition());
                assertEquals("end position", endpos, parser.getEndPos(result));
            }
            } catch (AssertionError e) {
                System.out.println(clazz + " " + startpos + " " + prefpos + " " + endpos);
                System.out.println(testString);
                if (e.getMessage().contains("failed to find")) Print.print(ztree);
                throw e;
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    ////////////////////////////////////////////////////////////////////////
    static int count = 0;
    
    public static class Test {
        boolean compunit;
        String input;
        Class<?> clazz;
        int numerrors;
        
        public Test(boolean cu, String input, Class<?> clazz, int numerrors) {
            this.compunit = cu;
            this.input = input;
            this.clazz = clazz;
            this.numerrors = numerrors;
        }
        
        public String toString() {
            String s = clazz.toString();
            return s + -((++count)+1)/2;
        }
    }
    
    // Put the # characters just before the start and pref and end positions, but note that
    // the end position is one after the end of the parser construct, so put the # just after
    // the end of the parser string
    static Object[][] tests = new Object[][]{
        { new Test(false,"2 + (##~ 1#) + 7", JCUnary.class, 0)},
        { new Test(false," (#2 #+ 1#) ", JCBinary.class, 0)},
        { new Test(false," (#true #? 1 : 2#) ", JCConditional.class, 0)},
        { new Test(false," (#true #==> false#) ", JmlBinary.class, 0)},
        { new Test(false,"2 + (##\\forall int x,y; 0 <= x; y == x#) + 7", JmlQuantifiedExpr.class, 0)},
        { new Test(true,"public class A { //@ ghost boolean i = ##true# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost int i = ##70# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost long i = ##70L# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost char i = ##'c'# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost String i = ##\"asd\"# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost double i = ##70.0# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost double i = ##70.0e1# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost int i = 2 + (##\\forall int x,y; 0 <= x; y == x#) + 7;\n }", JmlQuantifiedExpr.class, 0)},
        { new Test(true,"public class A { //@ assignable ##a[ *]#;\n void m(){}}", JmlStoreRefArrayRange.class, 0)},
        { new Test(true,"public class A { //@ assignable ##a[ 2 .. 4]#;\n void m(){}}", JmlStoreRefArrayRange.class, 0)},
        { new Test(true,"public class A { //@ assignable ##a[ 2 .. ]#;\n void m(){}}", JmlStoreRefArrayRange.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##abc# ;\n void m(){}}", JCIdent.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##ab . c# ;\n void m(){}}", JCFieldAccess.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##ab . *# ;\n void m(){}}", JCFieldAccess.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##\\nothing#;\n", JmlStoreRefKeyword.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##\\everything#;\n", JmlStoreRefKeyword.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##\\not_specified#;\n", JmlStoreRefKeyword.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##a, ab . *# ;\n void m(){}}", JmlStoreRefListExpression.class, 0)},
    };
    
    @org.junit.Test
    public void run() {
        helpParser(test.compunit, test.input, test.clazz, test.numerrors);
    }

}
