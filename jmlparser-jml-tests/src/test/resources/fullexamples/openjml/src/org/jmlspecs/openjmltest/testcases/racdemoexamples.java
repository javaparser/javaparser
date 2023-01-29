package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Before;
import org.junit.Test;

/**
 * These tests check running RAC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather
 * than immediately there in the test class.
 * <p>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racdemoexamples extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    public void helpFeature(String n, String... options) {
        helpTCF(OpenJMLDemoPath + "/src/examples/" + n, "test/racdemoexamples/" + n, "EntryPreconditionTest", options);
    }


    @Test
    public void EntryPrecondition() {
        expected_compile = "../expected_compile";
        helpFeature("EntryPrecondition", "-racCheckAssumptions", "-racPreconditionEntry");
    }

}
