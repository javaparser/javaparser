package org.jmlspecs.openjmltest.boogie;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
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

@RunWith(ParameterizedWithNames.class)
public class boogiefiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public boogiefiles(String options, String solver) {
        super(options,solver);
    }
    
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        super.setUp();
    	ignoreNotes = true;
    }
    
    @Parameters
    static public Collection<String[]> solversOnly() {
        return makeParameters(solvers);
    }

    
    public void helpTF(String testDirname, String ... opts) {
        String d = BOOGIEPATH + testDirname;
        String[] extraopts = new String[] {
                                "-lang=javelyn",
                                "-boogie",
                                "-normal",
                                "-checkFeasibility=none",
        };
        String[] newopts = new String[opts.length+extraopts.length];
        System.arraycopy(opts,0,newopts,0,opts.length);
        System.arraycopy(extraopts,0,newopts,opts.length,extraopts.length);
        helpTCF(d,d,newopts);
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        escOnFiles(sourceDirname,BOOGIEPATH,opts);
    }


    static String BOOGIEPATH = "/Users/davidcok/brazilws/src/Boogie/tests/files/";


    @Test
    public void javelyn0() {
        expectedExit = 0;
        helpTF("javelyn0.java");
    }

    @Test
    public void javelyn1() {
        expectedExit = 0;
        helpTF("javelyn1.java");
    }

    @Test
    public void javelyn2() {
        expectedExit = 0;
        helpTF("javelyn2.java");
    }

    @Test
    public void javelyn3() {
        expectedExit = 0;
        helpTF("javelyn3.java","-show","-method=n");
    }

    @Test
    public void javelynBreak() {
        expectedExit = 0;
        helpTF("javelynBreak.java");
    }

    @Test
    public void javelynBreakB() {
        expectedExit = 0;
        helpTF("javelynBreakB.java","-show");
    }


}
