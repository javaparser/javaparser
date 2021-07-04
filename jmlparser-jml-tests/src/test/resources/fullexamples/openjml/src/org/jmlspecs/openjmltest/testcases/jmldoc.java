package org.jmlspecs.openjmltest.testcases;

import java.io.ByteArrayOutputStream;

import java.io.PrintStream;

import org.junit.*;
import org.junit.rules.TestName;

import static org.junit.Assert.*;


/** This class contains tests of the jmldoc functionality.  It calls the actual
 * jmldoc entry point on external java files.
 * @author David Cok
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class jmldoc {
    @Rule
    public TestName name = new TestName();

    ByteArrayOutputStream berr;
    ByteArrayOutputStream bout;
    PrintStream savederr;
    PrintStream savedout;
    static String eol = System.getProperty("line.separator");
    static String z = java.io.File.pathSeparator;
    boolean print = false;
    boolean capture = true;
    
    @Before
    public void setUp() throws Exception {
        //capture = false;
        //print = true;
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    @After
    public void tearDown() {
        berr = null;
        bout = null;
        System.setErr(savederr);
        System.setOut(savedout);
    }
    
    /** This is a helper method that runs the compiler on the given set of
     * command-line arguments, checking the result
     * @param args the command-line arguments
     * @param exitcode the expected exit code (0=OK, 1=completed with error messages
     *      2=command-line problems, 3=system errors, 4=abort)
     * @param all whether the expected output is all of (0) or just the prefix
     *      of (1) or a part of (2) the actual output
     * @param output the expected output as one string
     */
    public void helper(String[] args, int exitcode, int all, String ... output) {
        int e = 4; // org.jmlspecs.openjml.jmldoc.Main.execute(args);
        System.err.flush();
        System.out.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualOutput = capture ? bout.toString() : "";
        String errOutput = capture ? berr.toString() : "";
        if (print) System.out.println("EXPECTING: " + output[0]);
        if (capture) try {
            String tail = ""; //exitcode == 0 ? "" : "ENDING with exit code " + exitcode + eol;
            if (print) System.out.println("TEST: " + name.getMethodName() + " exit=" + e + eol + errOutput);
            String expected = output[0];
            if (all==0) assertEquals("The error message is wrong",expected+tail,errOutput);
            else if (all == -1) assertEquals("The error message is wrong",expected,errOutput);
            else if (all == 1 && !errOutput.startsWith(expected)) {
                fail("Output does not begin with: " + expected + eol + "Instead is: " + errOutput);
            } else if (all == 2 && errOutput.indexOf(expected) == -1 ) {
                fail("Output does not end with: " + expected + eol + "Instead is: " + errOutput);
            }
            if (output.length > 1) {
                expected = output[1];
                if (print) System.out.println("TEST: " + name.getMethodName() + " STANDARD OUT: " + eol + actualOutput);
                if (all == 0) {
                    assertEquals("The standard out is wrong",expected+tail,actualOutput);
                } else if (all == -1) {
                    assertEquals("The standard out is wrong",expected,actualOutput);
                } else if (all == 2 && actualOutput.indexOf(expected) == -1) {
                    fail("Output does not end with: " + expected + eol + "Instead is: " + actualOutput);
                }
            }
            assertEquals("The exit code is wrong",exitcode,e);
        } catch (AssertionError ex) {
            if (!print) System.out.println("TEST: " + name.getMethodName() + " exit=" + e + eol + actualOutput);
            throw ex;
        }
    }

    // FIXME - ignoring all jmldoc tests until jmldoc is implemented
    
    @Test @Ignore
    public void testTopLevelCompiler() throws Exception {
        String failureMessage = "error: An entry point in org.jmlspecs.openjml.jmldoc.Main was called with a null argument" + eol;
        helper(null,2,-1,failureMessage);
    }
    
    @Test @Ignore
    public void testNoArgs() throws Exception {
        String failureMessage = "Usage: jmldoc <options> <source files>" + eol +
                                "where possible options include:" + eol;
        helper(new String[]{},1,1,"",failureMessage);
    }
    
    @Test @Ignore
    public void testHelp() throws Exception {
        String failureMessage = "Usage: jmldoc <options> <source files>" + eol +
                                "where possible options include:" + eol;
        helper(new String[]{"-help"},0,1,"",failureMessage);
    }
    
// FIXME - for some reason this works standalone, but fails when in sequence
    @Test @Ignore
    public void testBadOption() throws Exception {
        String failureMessage = "jmldoc: error - invalid flag: -ZZZ" + eol;
        String out = "usage: jmldoc [options] [packagenames] [sourcefiles] [@files]" + eol;
        helper(new String[]{"-ZZZ"},1,1,failureMessage,out);
    }
    
    /** Tests setting the specs path through the command-line option, by using non-existent 
     * directories that then get complaints
     * @throws Exception
     */
    @Test @Ignore // FIXME - Behaves differently when run standalone vs. run with the other tests
    public void _testSpecPath() throws Exception {
        helper(new String[]
                  {"-classpath","cpath"+z+"cpath2","-sourcepath","spath","-specspath","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z","P"},
                  0,
                  1,
                  "",
//                  "jmldoc: warning - No source files for package P" + eol +
//                  "jmldoc: warning - No source files for package P" + eol +
//                  "jmldoc: error - No public or protected classes found to document.",

                  "warning: A specification path directory does not exist: A" + eol +
                  "warning: A specification path directory does not exist: cpath" + eol +
                  "warning: A specification path directory does not exist: cpath2" + eol +
                  "warning: A specification path directory does not exist: spath" + eol +
                  "warning: A specification path directory does not exist: Z" + eol
                  );
    }
    
    // FIXME - disabled tests - jmldoc not implemented
    @Test @Ignore
    public void testRecursiveCP() throws Exception {
        helper(new String[]
                          { "-classpath","test/testNoErrors"+z+"bin"+z+"$CP",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"warning: $CP is included in the specs path recursively or multiple times"+eol
                          + "1 warning" + eol);
    }

    // TODO: Environment specific - backslashes
    @Test @Ignore
    public void testNoRuntime() throws Exception {
        helper(new String[]
                          { "-noInternalRuntime","-noInternalSpecs",
                            "-classpath","test/testNoErrors",
                            "test/testNoErrors/A.java",  
                          },1,0,
                          "test\\testNoErrors\\A.java:1: package org.jmlspecs.lang does not exist"+eol+
                          "public class A {" +eol+
                          "^"+eol+
                          "1 error" + eol+
                          "");
    }

    @Test @Ignore
    public void testDuplicateParse() throws Exception {
        helper(new String[]
                          { "-classpath","test/testNoErrors"+z+"bin",
                            "test/testNoErrors/A.java", "-jmlverbose", "-noInternalSpecs" 
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/test/testNoErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/test/testNoErrors/A.refines-java" + eol +
                          "typechecking A" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    @Test @Ignore
    public void testIgnoreJava() throws Exception {
        helper(new String[]
                          { "-classpath","test/testJavaErrors"+z+"bin",
                            "test/testJavaErrors/A.java", "-jmlverbose", "-noInternalSpecs"
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/test/testJavaErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/test/testJavaErrors/A.refines-java" + eol +
                          "typechecking A" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    @Test @Ignore
    public void testSourcePath() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","test/testNoErrors"+z+"runtime",
                            "-specspath","runtime",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * @throws Exception
     */
    @Test @Ignore
    public void testSourcePathX() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "test/testNoErrors/A.java"
                          },0,0,
                          "Note: Some input files use unchecked or unsafe operations."+eol+
                          "Note: Recompile with -Xlint:unchecked for details."+eol);
    }

    @Test @Ignore
    public void testSourcePath3() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","test/testNoErrors"+z+"runtime",
                            "-specspath","",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    // This test requires jmlruntime.jar to have been created - run the Makefile
    // in the OpenJML project
    @Test @Ignore
    public void testSourcePath4() throws Exception {
        helper(new String[]
                          { "-classpath","jmlruntime.jar",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    @Test @Ignore
    public void testSourcePath5() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java", 
                          },0,0,"",
                          "");
    }

    @Test @Ignore
    public void testSourcePath2() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","runtime",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java"
                          },1,0,"",  // FIXME - exit code should really be 0
                          "");
    }

    @Test @Ignore
    public void testSuperRead() { // TODO - file name is environment dependent
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "test/testSuperRead/A.java"
                          },1,1
                          ,""
                          ,"test\\testSuperRead\\B.refines-java:3: This JML modifier is not allowed for a type declaration"
                          );
    }
    
    // FIXME - need to chjeck that the output of these two is correct
    
//    @Test @Ignore
//    public void testAPI() {
//        System.setErr(savederr);
//        System.setOut(savedout);
//        try {
//            java.io.File f = new java.io.File("test/testNoErrors/A.java");
//            org.jmlspecs.openjml.Main m = new org.jmlspecs.openjml.Main(new String[]{});
//            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
//            System.out.println(s);
//        } catch (Exception e) {
//            System.out.println(e);
//            e.printStackTrace(System.out);
//        }
//    }
//    @Test @Ignore
//    public void testAPI2() {
//        System.setErr(savederr);
//        System.setOut(savedout);
//        try {
//            java.io.File f = new java.io.File("test/testNoErrors/A.java");
//            org.jmlspecs.openjml.Main m = new org.jmlspecs.openjml.Main(new String[]{"-v"});
//            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
//            System.out.println(s);
//        } catch (Exception e) {
//            System.out.println(e);
//            e.printStackTrace(System.out);
//        }
//    }
}
