package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.Ignorable;

/** These tests check running RAC on files in the file system, comparing the
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

// @RunWith(Ignorable.class)
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnonpublic extends RacBase {

	boolean nonpublicPresent;
	
    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
//        Assert.fail();
        Assume.assumeTrue( new File(OpenJMLDemoPath).exists() );
    }


    @Test @Ignore // not working yet
    public void racSokoban() {
        String dir = OpenJMLDemoPath + "/src/sokoban/src";
        expectedExit = 0;
        expectedRACExit = 1;
        helpTCF(dir,dir,"Game","-cp",dir,"-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban2() {
        String dir = OpenJMLDemoPath + "/src/sokoban2/src";
        expectedExit = 0;
        expectedRACExit = 1;
        ignoreNotes = true;
        helpTCF(dir,dir,"Game","-cp",dir,"-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban3() {
        String dir = OpenJMLDemoPath + "/src/sokoban3/src";
        expectedExit = 0;
        expectedRACExit = 1;
        ignoreNotes = true;
        helpTCF(dir,dir,"Game","-cp",dir,"-progress");
    }

    @Test @Ignore // not working yet
    public void racSokoban3Bug() {  // FIXME - currently the expected result says too big for a try statement, but originally it had a crash
        String dir = OpenJMLDemoPath + "/src/sokoban3/src";
        expectedExit = 1;
        runrac = false;
        expectedRACExit = 0;
        helpTCF(dir,dir+"/../bug","Game","-cp",dir,"-progress","-racJavaChecks");
    }


}
