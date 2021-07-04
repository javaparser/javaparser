package org.jmlspecs.openjmltest.testcases;
import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escDemofiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public escDemofiles(String options, String solver) {
        super(options,solver);
    }
    
    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    }

    /** This method does the running of a RAC test.  No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param dirname The directory containing the test sources, a relative path
     * from the project folder
     * @param classname The fully-qualified classname for the test class (where main is)
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	escOnFiles(sourceDirname,outDir,opts);
    }

    public java.util.List<String> setupForFiles(String sourceDirname, String outDir, String ... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-esc");
        args.add("-jmltesting");
        args.add("-no-purityCheck");
        args.add("-dir");
        args.add(sourceDirname);
        addOptionsToArgs(options,args);
        args.addAll(Arrays.asList(opts));
        return args;
    }
    


    @Test
    public void testInvertInjection() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/verifythis/InvertInjection.java","test/demoInvertInjection","-progress","-noInternalSpecs");
    }

    @Test
    public void testBinarySearch() {
        Assume.assumeTrue(runLongTests);
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/verifythis/BinarySearch.java","test/demoBinarySearch","-progress","-noInternalSpecs","-logic=AUFNIRA");
    }

    @Ignore  // FIXME: Fails because of inadequate specs and use of \created
    @Test
    public void testCustomer() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/verifythis/Customer.java","test/demoCustomer","-progress","-noInternalSpecs");
    }

    @Test
    public void testMaxByElimination() {
        expectedExit = 0;
        ignoreNotes = true;
        helpTCF(OpenJMLDemoPath + "/src/openjml/verifythis/MaxByElimination.java","test/demoMaxByElimination","-progress","-code-math=bigint");
    }

    @Test @Ignore // FIXME: Cannot reason about \sum
    public void testSumAndMax() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/verifythis/SumAndMax.java","test/demoSumAndMax","-progress");
    }

    @Test
    public void testEscTest() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/misc1/EscTest.java","test/demoEscTest","-progress","-jmltesting");
    }


}
