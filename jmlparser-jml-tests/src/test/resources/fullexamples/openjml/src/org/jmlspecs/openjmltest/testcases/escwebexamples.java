package org.jmlspecs.openjmltest.testcases;

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
import org.junit.FixMethodOrder;
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
public class escwebexamples extends EscBase {

    boolean enableSubexpressions = false;
    
    public escwebexamples(String options, String solver) {
        super(options,solver);
    }
    
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    	ignoreNotes = true;
    }
    
    public void helpTF(String testFileroot, String ... opts) {
        String d = "../../../openjml.github.io/examples/";
        int extraOpts = 3;
        String[] newopts = new String[opts.length+extraOpts];
        // Fill in exactly 'extraOpts' initial elements
        newopts[0] = "-classpath";
        newopts[1] = d;
        newopts[2] = "-solver-seed=42";
//        newopts[2] = "-checkFeasibility=precondition,reachable,exit,spec";
//        newopts[3] = "-code-math=bigint"; // Just to avoid overflow errors in these tests
//        newopts[4] = "-spec-math=bigint"; // Just to avoid overflow errors in these tests
        System.arraycopy(opts,0,newopts,extraOpts,opts.length);
        escOnFile(d + testFileroot + ".java", "test/webexamples/" + testFileroot, newopts);
    }

    public void helpTG(String ... opts) {
        helpTF(getMethodName(1), opts);
    }

    
    @Test  // This one non-deterministically timesout - hence the fixing of solver-seed
    public void HeapSort() {
        helpTG();
    }

    @Test
    public void SelectionSort() {
        helpTG();
    }

    @Test
    public void BubbleSort() {
        helpTG();
    }

    @Test
    public void MergeSort() {
        helpTG();
    }

 
}
