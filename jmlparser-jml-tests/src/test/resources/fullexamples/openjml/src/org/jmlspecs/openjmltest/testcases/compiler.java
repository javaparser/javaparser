package org.jmlspecs.openjmltest.testcases;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.jmlspecs.openjmltest.JmlTestCase;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;

/** Tests running the tool as if from the command-line (for typechecking);
 * includes erroneous command-line argument combinations and combinations
 * of class, source, and specs paths. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class compiler {
    
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
    String projHome = System.getProperty("openjml.eclipseProjectLocation").replace("C:","").replace("\\","/");
    String specsHome;
    {
    	try {
    		specsHome = new java.io.File("../../Specs").getCanonicalPath().replace("\\", "/");
    	} catch (Exception e) {
    		specsHome = null;
    	}
    }
    String expectedFile = null;
    
    @Before
    public void setUp() throws Exception {
        //capture = false; print = true;
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    @After
    public void tearDown() {
        // Do this just in case the test fails without having reset the streams
        berr = null;
        bout = null;
        System.setErr(savederr);
        System.setOut(savedout);
    }
    
    /** This is a helper method that runs the compiler on the given set of
     * command-line arguments, checking the result
     * @param args the command-line arguments
     * @param expectedExitCode the expected exit code (0=OK, 1=completed with error messages
     *      2=command-line problems, 3=system errors, 4=abort)
     * @param all whether the expected output is all of (0) or just the prefix
     *      of (1) or a part of (2) the actual output
     * @param output the expected output as one string; if there are two Strings,
     * then they are the expected error and standard output 
     */
    public void helper(String[] args, int expectedExitCode, int all, String ... output) {
        int exitCode = org.jmlspecs.openjml.Main.execute(args);
        System.err.flush();
        System.out.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        if (berr == null) return;
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualOutput = bout.toString();
        String errOutput = berr.toString();
        actualOutput = actualOutput.replace("\\","/");
        //actualOutput = actualOutput.replaceAll("temp-release/", "");
        errOutput = errOutput.toString().replace("\\","/");
        
        String expected;
        if (expectedFile != null) {
        	try {
        		expected = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(expectedFile)));
        		expected = JmlTestCase.doReplacements(expected.replace("../testfiles","testfiles"));
        	} catch (Exception ee) {
        		expected = null;
        		org.junit.Assert.fail(ee.toString());
        	}
        } else {
            expected = output[0];
        }
        expected = JmlTestCase.doReplacements(expected.replace("${PROJ}",projHome));
        actualOutput = actualOutput.replace("\r", "");
        errOutput = errOutput.replace("\r", "");
        expected = expected.replace("\r", "");
        actualOutput = removeNotes(actualOutput);
        
        if (print) System.out.println("EXPECTING: " + output[0]);
        print = false;
        if (print) System.out.println("ACTUAL OUT: " + actualOutput);
        if (print) System.out.println("ACTUAL ERR: " + errOutput);
        if (output.length <= 1 && errOutput.length() == 0 && !actualOutput.startsWith("Note:")) errOutput = actualOutput;
        if (capture) try {
            String tail = "";
            if (print) System.out.println("TEST: " + name.getMethodName() + " exit=" + exitCode + eol + errOutput);
            if (all==0) assertEquals("The error message is wrong",expected+tail,errOutput);
            else if (all == -1) assertEquals("The error message is wrong",expected,errOutput);
            else if (all == 1 && !actualOutput.startsWith(expected)) {
                fail("Output does not begin with: " + expected + eol + "Instead is: " + errOutput);
            } else if (all == 2 && actualOutput.indexOf(expected) == -1 ) {
                fail("Output does not end with: " + expected + eol + "Instead is: " + errOutput);
            }
            if (output.length > 1) {
                expected = output[1].replace("${PROJ}",projHome).replaceAll("\r", "");
                int k = actualOutput.indexOf("Note:");
                String actual = k>=0 ? actualOutput.substring(0,k) : actualOutput; 
                if (print) System.out.println("TEST: " + name.getMethodName() + " STANDARD OUT: " + eol + actual);
                if (all == 0) {
                    assertEquals("The standard out is wrong",expected+tail,actual);
                } else if (all == -1) {
                    assertEquals("The standard out is wrong",expected,actual);
                } else if (all == 1 && (actualOutput.indexOf(expected) == -1 && errOutput.indexOf(expected) == -1)) {
                    fail("Output does not contain: " + expected + eol + "Instead is: " + actual);
                }
            }
            assertEquals("The exit code is wrong",expectedExitCode,exitCode);
        } catch (AssertionError ex) {
            if (!print) {
                System.out.println("TEST: " + name.getMethodName() + " exit=" + exitCode + eol + berr.toString());
                System.out.println("ACTUAL OUT: " + actualOutput);
                System.out.println("ACTUAL ERR: " + errOutput);
            }
            throw ex;
        }
    }
    
    public String removeNotes(String input) {
        while (true) {
        	int p = input.indexOf("Note: ");
        	if (p < 0) break;
        	int q = input.indexOf("\n",p);
        	input = input.substring(0, p) + input.substring(q+1);
        }
        return input;
    }

    /** Tests a null argument for the args */
    @Test
    public void testTopLevelCompiler() throws Exception {
        String failureMessage = "error: The main entry point org.jmlspecs.openjml.Main.main was called with a null argument" + eol;
        helper(null,2,-1,failureMessage);
    }
    
    /** Test with no arguments at all (empty array for args), which should
     * produce the help message. */
    @Test
    public void testNoArgs() throws Exception {
        String failureMessage = "Usage: openjml <options> <source files>" + eol +
                                "where possible options include:" + eol;
        helper(new String[]{},2,1,"",failureMessage);
    }
    
    /** Tests an unknown option */
    @Test
    public void testBadOption() throws Exception {
        String failureMessage = "openjml: invalid flag: -ZZZ" + eol +
                                "Usage: openjml <options> <source files>" + eol + 
                                "use -help for a list of possible options" + eol;
        helper(new String[]{"-ZZZ"},2,0,failureMessage);
    }
    
    /** Tests a bad command */
    @Test
    public void testBadCommand() throws Exception {
        String failureMessage = "error: Invalid parameter to the -command option: zzz" + eol;
        helper(new String[]{"-command=zzz"},2,0,failureMessage);
    }
    
    /** Tests setting the specs path through the command-line option, by using non-existent 
     * directories that then get complaints
     * @throws Exception
     */
    @Test
    public void testSpecPath() throws Exception {
        helper(new String[]
                  {"-classpath","cpath"+z+"cpath2","-sourcepath","spath","-specspath","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z","-noPurityCheck","test/testNoErrors/A.java"},
                  0,
                  1,
//                  "openjml: file not found: A.java" + eol +
//                  "Usage: openjml <options> <source files>" + eol +
//                  "use -help for a list of possible options" + eol +
                  "warning: A specification path directory does not exist: A" + eol +
                  "warning: A specification path directory does not exist: cpath" + eol +
                  "warning: A specification path directory does not exist: cpath2" + eol +
                  "warning: A specification path directory does not exist: spath" + eol +
                  "warning: A specification path directory does not exist: Z" + eol
                  );
    }
    
    /** Tests a recursive definition for the specspath */
    @Test
    public void testRecursiveCP() throws Exception {
        helper(new String[]
                          { "-classpath","test/testNoErrors"+z+"bin"+z+"$CP",
                  //          "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"warning: $CP is included in the specs path recursively or multiple times"+eol
                          + "1 warning" + eol);
    }

    /** Tests the lack of a runtime library */
    @Test
    public void testNoRuntime() throws Exception {
        helper(new String[]
                          { "-noInternalRuntime","-noInternalSpecs",
                            "-classpath","test/testNoErrors",
                            "test/testNoErrors/A.java",  
                          },3,0,
                          "Fatal Error: Unable to find package org.jmlspecs.lang" + eol);
//                          "test/testNoErrors/A.java:1: error: package org.jmlspecs.lang does not exist"+eol+
//                          "public class A {" +eol+
//                          "^" + eol +
//                          "1 error" + eol);
    }

    /** Test verbose with no specs used */
    @Test
    public void testDuplicateParse() throws Exception {
        helper(new String[]
                          { "-classpath","test/testNoErrors"+z+"bin",
                            "test/testNoErrors/A.java", "-jmlverbose", "-noInternalSpecs" 
                          },0,2,"",
                          //"parsing ${PROJ}/test/testNoErrors/A.java" + eol +
                          //"parsing ${PROJ}/test/testNoErrors/A.refines-java" + eol +
                          "entering test/testNoErrors/A.java" + eol +
                          "  completed entering test/testNoErrors/A.java" + eol +
                          "typechecking A" + eol +
                          "No specs for java.lang.Object" + eol + 
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    
    /** Test that specs in the java file are ignored */
    @Test
    public void testIgnoreJava() throws Exception {
        helper(new String[]
                          { "-classpath","test/testJavaErrors"+z+"bin",
                            "test/testJavaErrors/A.java", "-jmlverbose", "-noInternalSpecs"
                          },0,2,"",
                          //"parsing ${PROJ}/test/testJavaErrors/A.java" + eol +
                          // stuff about specs path comes in here
                          //"parsing ${PROJ}/test/testJavaErrors/A.refines-java" + eol +
                          "entering test/testJavaErrors/A.java" + eol +
                          "  completed entering test/testJavaErrors/A.java" + eol +
                          "No specs for java.lang.annotation.Annotation" + eol +
                          "No specs for org.jmlspecs.annotation.Ghost" + eol +
                          "typechecking A" + eol +
                          "No specs for java.lang.Object" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    /** Test that the source path is used to find input java files */
    @Test
    public void testSourcePath() throws Exception {
        helper(new String[]
                          { "-classpath"," ",
                            "-sourcepath","test/testNoErrors"+z+"../OpenJML/runtime",
                            "-specspath","../OpenJML/runtime",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * Uses source for classpath.
     * @throws Exception
     */ // FIXME - clean up the unchecked casts
    @Test
    public void testSourcePathX() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",  //"-Xlint:unchecked",
                            "test/testNoErrors/A.java"
                          },0,0
                          ,""
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",
                            "test/testNoErrors/A.jml"
                          },0,0
                          ,""
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1() throws Exception {
        //print = true;
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testJavaErrors2",
                            "-specspath","../OpenJML/runtime"+z+"test/testJavaErrors2",
                            "-noPurityCheck",
                            "test/testJavaErrors2/A.java"
                          },1,1
                          ,"test/testJavaErrors2/A.java:2: error: incompatible types"
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1A() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testJavaParseErrors",
                            "-specspath","../OpenJML/runtime"+z+"test/testJavaParseErrors",
                            "-noPurityCheck",
                            "test/testJavaParseErrors/A.jml"
                          },1,1
                          ,"test/testJavaParseErrors/A.java:2: error: illegal start of expression"
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error - but in the JML, so it is ignored since there 
     * already is a specs file.
     * @throws Exception
     */ 
    @Test
    public void testJML1B() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testJavaErrors",
                            "-specspath","../OpenJML/runtime"+z+"test/testJavaErrors",
                            "-noPurityCheck",
                            "test/testJavaErrors/A.java"
                          },0,0,
                          ""
                          );
    }

    /** Tests having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML2() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath","test/testNoSource",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",
                            "test/testNoSource/A.jml"
                          },1,1
                          ,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSource/A.jml" + eol 
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML3() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath"," ",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",
                            "test/testNoErrors/A.jml"
                          },1,1
                          ,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoErrors/A.jml" + eol
                          );
    }

    @Test
    public void testJML4() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath"," ",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",
                            "test/testNoSourceParseError/A.jml"
                          },1,1
                          ,"test/testNoSourceParseError/A.jml:4: error: illegal start of expression" + eol +
                           "int i = ;" + eol +
                           "        ^" + eol +
                           "error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSourceParseError/A.jml" + eol
                          );
    }

    @Test
    public void testJML5() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime",
                            "-sourcepath"," ",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",
                            "test/testNoSourceTypeError/A.jml"
                          },1,1
                          ,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSourceTypeError/A.jml" + eol
                           );
    }

    // FIXME - the jml and class files do not match - we should get type errors
    @Test
    public void testJML6() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/runtime"+z+"test/testNoSourceWithClass",
                            "-sourcepath"," ",
                            "-specspath","../OpenJML/runtime"+z+"test/testNoSourceWithClass",
                            "-noPurityCheck",
                            "test/testNoSourceWithClass/A.jml"
                          },1,1
                          ,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSourceWithClass/A.jml" + eol 
                          );
    }

    /** Checks that -nowarn turns off warnings. */
    @Test
    public void testJML6nowarn() throws Exception {
        helper(new String[]
                                { "-classpath","../OpenJML/runtime",
                                  "-sourcepath","test/testNoErrors",
                                  "-specspath","../OpenJML/runtime",
                                  "-lang=jml",
                                  "-extensions=X","-nowarn", // Ignored when strict
                                  "test/testNoErrors/A.jml"
                                },0,0
                                ,""
                                );
    }

    /** Checks that -Werror turns warnings into errors cf. testExtension1*/
    @Test
    public void testJML6Werror() throws Exception {
        helper(new String[]
                                { "-classpath","../OpenJML/runtime",
                                  "-sourcepath","test/testNoErrors",
                                  "-specspath","../OpenJML/runtime",
                                  "-lang=jml",
                                  "-extensions=X","-Werror", // Ignored when strict
                                  "test/testNoErrors/A.jml"
                                },1,0
                                ,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The /count construct is an OpenJML extension to JML and not allowed under -lang=jml\n"
                                +"            //@ loop_invariant i == /count && 0 <= i <= values.length;\n"
                                +"                                    ^\n"
                                +"error: warnings found and -Werror specified"+eol
                                +"1 error"+eol
                                +"1 warning"+eol
                                );
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * Uses bin for classpath.
     * @throws Exception
     */
    @Test
    public void testSourcePathXB() throws Exception {
        helper(new String[]
                          { "-classpath","../OpenJML/bin-runtime",  // FIXME - needs annotations?
                            "-sourcepath","test/testNoErrors",
                            "-specspath","../OpenJML/runtime",
                            "-noPurityCheck",  //"-Xlint:unchecked",
                            "test/testNoErrors/A.java"
                          },0,0
                          ,""
                          );
    }

    /** Tests that specs files are not found with empty specs path */
    @Test
    public void testSourcePath3() throws Exception {
        helper(new String[]
                          { "-classpath"," ",
                            "-sourcepath","test/testNoErrors"+z+"../OpenJML/runtime",
                            "-specspath","",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    // This test requires jmlruntime.jar to have been created - run the Makefile
    // in the OpenJML project
    /** Tests using the runtime jar */
    //@Test  // FIXME - try running the build programmatically
    @Test 
    public void testSourcePath4() throws Exception {
        if (!new java.io.File("../OpenJML/tempjars/jmlruntime.jar").exists()) {
            System.setErr(savederr);
            System.setOut(savedout);
            System.out.println("The testSourcePath4 test depends on having a release version of jmlruntime.jar in the jars directory.  It will not be run until a release has been built.");
        } else {
            helper(new String[]
                          { "-classpath","../OpenJML/tempjars/jmlruntime.jar",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java",  
                          },0,0,"",
                          "");
        }
    }

    /** Tests using class, source and specs path */
    @Test
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

    @Test
    public void testSourcePath2() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","test/testNoErrors",
                            "-specspath","../OpenJML/runtime",
                            "-noInternalSpecs",
                            "test/testNoErrors/A.java"
                          },0,0,"",
                          "");
    }

    /** Tests that super files are read and processed */
    @Test
    public void testSuperRead() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "test/testSuperRead/A.java"
                          },1,1
                          ,""
                          ,"test/testSuperRead/B.jml:3: error: This JML modifier is not allowed for a type declaration"
                          );
    }
    
    /** Tests the -java option */
    @Test
    public void testJavaOption() {
        helper(new String[]
                          { "-java", 
                            "-classpath","test",
                            "test/testSpecErrors/A.java"
                          },0,0
                          ,""
                          ,"");
        
    }
    
    /** Tests the -java option must be first*/
    @Test
    public void testJavaOption2() {
        helper(new String[]
                          {  
                            "-classpath","test",
                            "-java",
                            "-noPurityCheck",
                            "test/testNoErrors/A.java"
                          },0,1
                          ,""
                          ,"The -java option is ignored unless it is the first command-line argument"
                          );
        
    }
    
    /** Tests that we get errors without the -java option */
    @Test
    public void testJavaOption1() {
        helper(new String[]
                          { "-classpath","test/testSpecErrors", 
                            "-noPurityCheck",
                            "test/testSpecErrors/A.java"
                          },1,0
                          ,""
                          ,"test/testSpecErrors/A.jml:4: error: incompatible types: boolean cannot be converted to int" + eol 
                          +"    //@ ghost int i = true; // Error to provoke a message" + eol 
                          +"                      ^" + eol
                          + "1 error" + eol
                          );
    }
    
    /** Tests an invalid use of key */
    @Test
    public void testKeys0() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "test/testKeys/D.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys1() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "test/testKeys/A.java"
                          },1,1
                          ,"test/testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys1a() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K2",
                            "test/testKeys/A.java"
                          },1,1
                          ,"test/testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys2() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K1",
                            "test/testKeys/A.java"
                          },0,1
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys3() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K2",
                            "test/testKeys/B.java"
                          },1,1
                          ,"test/testKeys/B.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys4() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "test/testKeys/B.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys4a() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K3",
                            "test/testKeys/B.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys5() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K4,K2",
                            "test/testKeys/C.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys6() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","test",
                            "-specspath","test",
                            "-noPurityCheck",
                            "-keys","K2,K3",
                            "test/testKeys/C.java"
                          },1,1
                          ,"test/testKeys/C.java:10: error: cannot find symbol"
                          ,""
                          );
    }
    
    @Test
    public void testModelBug() throws Exception {
        helper(new String[]
                          { "-noPurityCheck",  //"-Xlint:unchecked",
                            "test/model1/ModelClassExampleBug.java",
                            "test/model1/ModelClassExampleBugSub.java",
                            "test/model1/ModelClassExampleBugSub2.java"
                          },1,0
                          ,"test/model1/ModelClassExampleBugSub.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "    public static class SIndexedContents extends ModelClassExampleBug<E>.SContents { // ERROR" + eol +
                           "                                                                      ^" + eol +
                           "test/model1/ModelClassExampleBugSub2.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "        public static model class SMIndexedContents extends ModelClassExampleBug<E>.SMContents { // ERROR" + eol +
                           "                                                                                 ^" + eol +
                           "2 errors" + eol
                          );
    }

    @Test
    public void testModelBug2() throws Exception {
        helper(new String[]
                          { "-noPurityCheck",  //"-Xlint:unchecked",
                            "test/model2/NonGenericModelClassExampleBug.java",
                            "test/model2/NonGenericModelClassExampleBugSub.java",
                          },0,0
                          ,""
                          ,""
                          );
    }

    @Test
    public void testExtension1() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML/runtime",
                  "-sourcepath","test/testNoErrors",
                  "-specspath","../OpenJML/runtime",
                  "-lang=jml",
                  "-extensions=X", // Ignored when strict
                  "test/testNoErrors/A.jml"
                },0,0
                ,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The /count construct is an OpenJML extension to JML and not allowed under -lang=jml\n"
                +"            //@ loop_invariant i == /count && 0 <= i <= values.length;\n"
                +"                                    ^\n"
                +"1 warning\n");
    }

    @Test
    public void testExtension2() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML/runtime",
                  "-sourcepath","test/testNoErrors",
                  "-specspath","../OpenJML/runtime",
                  "-extensions=X",
                  "test/testNoErrors/A.jml"
                },1,1
                ,"error: Failed to load extension X: No such package found"
                ,""
                );
    }

    @Test @Ignore // FIXME - have not yet fixed how extensions are found
    public void testExtension3() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML/runtime",
                  "-sourcepath","test/testext",
                  "-specspath","../OpenJML/runtime",
                  "-extensions=ext",
                  "test/testext/A.java"
                },0,0
                ,""
                );
    }
    // FIXME - check the version
    // FIXME - testOK2, testOK3, testJmlBad2
    // FIXME - test RAC-OK, SIMPLE, etc.
    
    @Test
    public void release_testJmlHelp() throws Exception {
    	expectedFile = "releaseTests/testJmlHelp/expected";
    	helper(new String[]
                { 
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlHelp2() throws Exception {
    	expectedFile = "releaseTests/testJmlHelp/expected";
    	helper(new String[]
                { "-help"
                },0,0
                ,""
                );
    }

    @Test
    public void release_testJmlBad() throws Exception {
    	expectedFile = "releaseTests/testJmlBad/expected";
    	helper(new String[]
                { "-verboseness="
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBad_A() throws Exception {
    	expectedFile = "releaseTests/testJmlBadA/expected";
    	helper(new String[]
                { "-verboseness"
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBad_B() throws Exception {
    	expectedFile = "releaseTests/testJmlBad/expected";
    	helper(new String[]
                { "-verboseness", ""
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBad_C() throws Exception {
    	expectedFile = "releaseTests/testJmlBad/expected";
    	helper(new String[]
                { "-verboseness= "
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBad3() throws Exception {
    	expectedFile = "releaseTests/testJmlBad3/expected";
    	helper(new String[]
                { "-check","-java"
                },2,0
                ,""
                );
    }

    @Test
    public void release_testOK1() throws Exception {
    	helper(new String[]
    			{ "-noPurityCheck","-specspath","releaseTests/testOK1","temp-release/B.java"
    			},0,0
    			,""
    			);
    }

    @Test
    public void release_testOK4() throws Exception {
    	helper(new String[]
    			{ "-noPurityCheck","-specspath","releaseTests/testOK1","temp-release/B.java","-noInternalSpecs"
    			},0,0
    			,""
    			);
    }
    
    // Testing typechecking without org.jmlspecs.annotation.*
    @Test
    public void release_testRuntime1() throws Exception {
    	expectedFile = "releaseTests/testRuntime1/expected";
    	helper(new String[]
    			{ "temp-release/C.java", "-jmltesting", "-classpath", ".", "-no-purityCheck", "-no-internalRuntime"
    			},3,0
    			,""
    			);
    }
    
    // Testing typechecking with binary files for org.jmlspecs.annotation.*
    @Test
    public void release_testRuntime2() throws Exception {
    	expectedFile = "releaseTests/testRuntime2/expected";
    	helper(new String[]
    			{ "temp-release/C.java", "-classpath", "../../JMLAnnotations/bin"+z+"../OpenJML/bin-runtime", "-no-purityCheck", "-no-internalRuntime"
    			},0,0
    			,""
    			);
    }
    
    // Testing typechecking with source files for org.jmlspecs.annotation.*
    @Test
    public void release_testRuntime3() throws Exception {
    	expectedFile = "releaseTests/testRuntime3/expected";
    	helper(new String[]
    			{ "temp-release/C.java",  "-classpath", "../../JMLAnnotations/src"+z+"../OpenJML/runtime", "-no-purityCheck", "-no-internalRuntime"
    			},0,0
    			,""
    			);
    }
    
    // Testing typechecking with normal internal libaries
    @Test
    public void release_testRuntime4() throws Exception {
    	expectedFile = "releaseTests/testRuntime4/expected";
    	helper(new String[]
    			{ "temp-release/C.java", "-no-purityCheck",
    			},0,0
    			,""
    			);
    }
    
    // Testing typechecking with normal internal libaries
    @Test
    public void release_testRuntime5() throws Exception {
    	expectedFile = "releaseTests/testRuntime5/expected";
    	helper(new String[]
    			{ "temp-release/D.java", "-no-purityCheck",
    			},0,0
    			,""
    			);
    }
    
    @Test
    public void release_testEsc1() throws Exception {
    	expectedFile = "releaseTests/testEsc1/expected";
    	helper(new String[]
    			{ "-no-purityCheck", "-esc", "testfiles/testEsc/A.java", "-classpath", "testfiles/testEsc"
    			},0,0
    			,""
    			);
    }
    
    @Test
    public void release_testEsc2() throws Exception {
    	expectedFile = "releaseTests/testEsc2/expected";
    	helper(new String[]
    			{ "-no-purityCheck", "-esc", "testfiles/testEsc/B.java", "-classpath", "testfiles/testEsc"
    			},0,0
    			,""
    			);
    }
    
    @Test
    public void release_testPath1() throws Exception {
    	expectedFile = "releaseTests/testPath1/expected";
    	helper(new String[]
    			{ "-jmltesting", "-no-purityCheck", "testfiles/testPath/data/TestPath.java", 
    			},1,0
    			,""
    			);
    }
    
    @Test
    public void release_testPath2() throws Exception {
    	expectedFile = "releaseTests/testPath2/expected";
    	helper(new String[]
    			{ "-jmltesting", "-no-purityCheck", "testfiles/testPath/data/TestPath.java", "-classpath", "testfiles/testPath/data"
    			},1,1
    			,""
    			);
    }
    
    @Test
    public void release_testPath3() throws Exception {
    	expectedFile = "releaseTests/testPath3/expected";
    	helper(new String[]
    			{ "-jmltesting", "-no-purityCheck", "testfiles/testPath/data/TestPath.java", "-specspath", "testfiles/testPath/data-specs"
    			},1,1
    			,""
    			);
    }
    
    @Test
    public void release_testPath4() throws Exception {
    	expectedFile = "releaseTests/testPath4/expected";
    	helper(new String[]
    			{ "-jmltesting", "-no-purityCheck", "testfiles/testPath/data/TestPath.java", "-sourcepath", "testfiles/testPath/data-specs" 
    			},1,0
    			,""
    			);
    }
    
    // FIXME - rest of testPath release tests

}
