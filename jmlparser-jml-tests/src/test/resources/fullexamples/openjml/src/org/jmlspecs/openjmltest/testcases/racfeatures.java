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
import org.junit.Before;
import org.junit.Test;

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

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfeatures extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpFeature(String n, String ... options) {
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/racfeatures/"+n,"features."+n, options);
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/racfeatures/"+n+"R","features."+n, "-racJavaChecks");
    }
    
    
    @Test
    public void NegativeArraySize() {
        expectedRACExit = 1;
        helpFeature("NegativeArraySize");
    }

    @Test
    public void JavaAssertion() {
        expectedRACExit = 1;
        helpFeature("JavaAssertion");
    }

    @Test
    public void ArrayStore() {
        expectedRACExit = 0;
        helpFeature("ArrayStore");
    }


}
