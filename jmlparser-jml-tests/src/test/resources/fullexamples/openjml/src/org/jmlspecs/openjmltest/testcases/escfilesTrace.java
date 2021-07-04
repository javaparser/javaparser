package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
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
@Ignore // FIXME - improve and stabilize trace output
public class escfilesTrace extends EscBase {

    boolean enableSubexpressions = false;
    
    public escfilesTrace(String options, String solver) {
        super(options,solver);
    }
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    }

    public java.util.List<String> setupForFiles(String sourceDirname, String outDir, String ... opts) {
    	ignoreNotes = true;
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-esc");
        args.add("-noPurityCheck");
        args.add("-jmltesting");
        if (new File(sourceDirname).isDirectory()) args.add("-dir");
        args.add(sourceDirname);
        if (solver != null) args.add("-prover="+solver);
        addOptionsToArgs(options,args);        
        args.addAll(Arrays.asList(opts));
        return args;
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
 //   	Assert.fail();
    	escOnFiles(sourceDirname,outDir,opts);
    }

    String OpenJMLDemoNonPublicPath = "../OpenJMLDemo";

    @Test 
    public void testDMZCashTrace() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoNonPublicPath + "/src/dmz2","test/escDmz2Trace","-subexpressions","-method=dmz2.Cash.Cash","-escMaxWarnings=1","-jmltesting");
    }



    @Test // @Ignore // Ignoring for now because the output is too volatile, even if correct - lots of paths that can be found in various orders
    public void testDemoPaths() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Paths.java","test/escDemoPaths","-subexpressions","-progress");
    }

    @Test 
    public void testDemoChangeCase() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/ChangeCase.java","test/escDemoChangeCase","-noInternalSpecs","-progress","-method=changeCase","-escMaxWarnings=1","-subexpressions","-jmltesting");
    }

    @Test
    public void testTrace() {
        expectedExit = 0;
        helpTCF("test/escTrace","test/escTrace",
                "-method=m","-escMaxWarnings=1",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testTrace2() {
        expectedExit = 0;
        helpTCF("test/escTrace2","test/escTrace2","-method=m", enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testTrace3() {
        expectedExit = 0;
        helpTCF("test/escTrace3","test/escTrace3","-progress", enableSubexpressions ? "-subexpressions" : "", "-jmltesting");
    }

    @Test
    public void testTrace4() {
        expectedExit = 0;
        helpTCF("test/escTrace4","test/escTrace4","-method=m","-subexpressions","-progress");
    }

    @Test
    public void testTrace5() {
        expectedExit = 0;
        helpTCF("test/escTrace5","test/escTrace5","-method=m","-progress", enableSubexpressions ? "-subexpressions" : "","-jmltesting");
    }

    @Test
    public void testTrace6() {
        expectedExit = 0;
        helpTCF("test/escTrace6","test/escTrace6","-progress", "-subexpressions","-jmltesting");
    }

    @Test
    public void testTraceloops() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops","-method=mgood","-progress", "-subexpressions","-jmltesting");
    }

    @Test
    public void testTraceloops1() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops1","-method=m1","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceloops2() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops2","-method=m2","-subexpressions","-progress");
    }

    @Test
    public void testTraceloops3() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops3","-method=m3","-progress", enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testTraceloops4() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops4","-method=m4","-progress", enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testTraceloops5() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops5","-method=m5","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceloops6() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceLoops6","-method=m6","-subexpressions","-progress");
    }

    @Test
    public void testTraceWhile() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceWhile","-method=mwhile","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceWhile1() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceWhile1","-method=mwhile1","-subexpressions","-progress");
    }

    @Test
    public void testTraceWhile2() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceWhile2","-method=mwhile2","-subexpressions","-progress");
    }

    @Test
    public void testTraceDo() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceDo","-method=mdo","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceDo1() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceDo1","-method=mdo1","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceDo2() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceDo2","-method=mdo2","-subexpressions","-progress");
    }

    @Test
    public void testTraceForeach() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach","-method=mforeach","-subexpressions","-progress");
    }

    @Test
    public void testTraceForeach1() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach1","-method=mforeach1","-subexpressions","-progress");
    }

    @Test
    public void testTraceForeach2() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach2","-method=mforeach2","-subexpressions","-progress");
    }

    @Test
    public void testTraceForeach3() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach3","-method=mforeach3","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testTraceForeach4() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach4","-method=mforeach4","-subexpressions","-progress");
    }

    @Test
    public void testTraceForeach5() {
        expectedExit = 0;
        helpTCF("test/escTraceLoops","test/escTraceForeach5","-method=mforeach5","-subexpressions","-progress");
    }

    @Test
    public void testTraceBS() {
        expectedExit = 0;
        helpTCF("test/escTraceBS","test/escTraceBS","-subexpressions","-progress");
    }


}
