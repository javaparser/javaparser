package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjmltest.ParseBase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.junit.Ignore;
import org.junit.Test;

import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This set of tests test that the pretty printer outputs properly.  The test
 * checks this by comparing the input code to the output code; before comparison,
 * each sequence of white space is replaced by a single space, so that the 
 * output formatting does not have to precisely match the input (unless
 * precise is set true, which it currently is).
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class prettyprinting extends ParseBase {

    boolean precise = true;
    @Override
    public void setUp() throws Exception {
        super.setUp();
        print = false;
    }

    public void helpPP(String code) {
        try {
            //print = true;
            Log.instance(context).useSource(new TestJavaFileObject(code));
            Parser p = fac.newParser(code,false,true,true);
            //sc = ((JmlParser)p).getScanner();
            JCTree tree = p.parseCompilationUnit();
            String out = JmlPretty.write(tree);
            if (collector.getDiagnostics().size() != 0) printDiagnostics();
            assertEquals("Found parsing errors",0,collector.getDiagnostics().size());
            if (!precise) {
                code = code.replaceAll("[ \t\r\n]+"," ");
                out = out.replaceAll("[ \t\r\n]+"," ");
            } else {
                code = code.replaceAll("[\r]","");
                out = out.replaceAll("[\r]","");
            }
            if (print || !code.equals(out)) {
                System.out.println("IN:");
                System.out.print(code);
                System.out.println("OUT:");
                System.out.print(out);
                //printTree(ParseTreeScanner.walk(tree));
            }
            assertEquals("Output differs",code,out);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
    
    String eol = System.getProperty("line.separator");

    @Test
    public void testSimpleClass() {
        helpPP(
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testPackage() {
        helpPP(
                "package t;" + eol + 
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testImport() {
        helpPP(
                "package t;" + eol + 
                eol +
                "import java.io.File;" + eol +
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testImportStar() {
        helpPP(
                "package t;" + eol + eol +
                "import java.io.File;" + eol +
                "import java.io.*;" + eol + eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testModelImport() {
        helpPP(
                "package t;" + eol + eol +
                "//@ model import java.io.File;" + eol +
                "//@ model import java.io.*;" + eol + eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testClassModifiers() {
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "}"
        );
    }
   
    @Test
    public void testMethodDecl() {
        helpPP(
                eol +
                "public static final class A {" + eol +
                "  " + eol + 
                "  void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    @Test
    public void testMethodModifiers() {
        helpPP(
                eol + 
                "class A {" + eol + 
                "  " + eol + 
                "  public static void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    @Test
    public void testMethodStatements() {
        precise = true;
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "  " + eol + 
                "  int p(int a, Object o) {" + eol +
                "  }" + eol +
                "  " + eol +
                "  void m() {" + eol +
                "    int a;" + eol +
                "    a = 5;" + eol +
                "    ;" + eol + 
                "    a += 5;" + eol +
                "    /*@ assume a == 6;*/" + eol +
                "    /*@ assert a == 6;*/" + eol +
                "    /*@ debug a = 6;*/" + eol +
                "    /*@ set a = 6;*/" + eol +
                "    a += 5;" + eol +
                "    a -= 5;" + eol +
                "    a *= 5;" + eol +
                "    a /= 5;" + eol +
                "    a %= 5;" + eol +
                "    a |= 5;" + eol +
                "    a &= 5;" + eol +
                "    a ^= 5;" + eol +
                "    a <<= 5;" + eol +
                "    a >>= 5;" + eol +
                "    a >>>= 5;" + eol +
                "    m();" + eol +
                "    for (int i = 0; i < 5; i++) {" + eol +
                "    }" + eol +
                "    for (int i : new int[6]) {" + eol +
                "    }" + eol +
                "    while (true) {" + eol +
                "      do {" + eol +
                "      } while (true);" + eol +
                "    }" + eol +
                "    /*@ assert (* xyz *);*/" + eol +
                "  }" + eol +
                "}"
        );
    }
    
    @Test
    public void testMethodStatements2() {
        precise = false; // TODO
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "  " + eol + 
                "  void m() {" + eol +
                "    int a;" + eol +
                "    a = 5;" + eol +
                "    ;" + eol + 
                "    a += 5;" + eol +
                "    /*@ choose { a = 6; } or { assume a == 6; a = 7; } else { a = 7; } */" + eol +
                "  }" + eol +
                "}"
        );
    }
    
    // FIXME - need to test every construct (lots more) for pretty printing; also for with and without jml comments
   
}
