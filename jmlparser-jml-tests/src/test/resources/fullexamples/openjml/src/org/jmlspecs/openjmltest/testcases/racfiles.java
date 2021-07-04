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
import org.junit.Before;
import org.junit.Ignore;
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
public class racfiles extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
        ignoreNotes = true;
    }




    /** Testing without using system specs */
    @Test
    public void test1() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("test/rac1","test/rac1","Bug1","-noInternalSpecs");
    }

    /** Testing using system specs */
    @Test  // FIXME - problems with library specs - RAC cannot handle ghost variables when it does not compile the class file
    public void test1a() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("test/rac1a","test/rac1a","Bug1");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBug1() {
        expectedExit = 0;
        expectedRACExit = 1;
        helpTCF("test/racbug1","test/racbug1","Add");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBugStackTrace() {
        expectedExit = 0;
        helpTCF("test/racStackTrace","test/racStackTrace","CantCompileRAC");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint() {
        expectedExit = 0;
        helpTCF("test/racPoint","test/racPoint","Point","-quiet");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint2() {
        expectedExit = 0;
        helpTCF("test/racPoint2","test/racPoint2","Point");
    }

    @Test
    public void testFirstTest() {
        expectedExit = 0;
        helpTCF("test/firstTest","test/firstTest","FirstTest","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testUniqueList() {
        expectedExit = 0;
        helpTCF("test/uniqueList","test/uniqueList","UniqueList","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList1() {
        expectedExit = 0;
        helpTCF("test/uniqueListBug1","test/uniqueListBug1","UniqueListBug1","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList2() {
        expectedExit = 0;
        helpTCF("test/uniqueListBug2","test/uniqueListBug2","UniqueListBug2");
    }

    @Test
    public void testDecimal() {
        expectedExit = 0;
        helpTCF("test/sv_rac","test/sv_rac","sv_rac/Decimal");
    }

    @Test
    public void testDecimal2() {
        expectedExit = 0;
        helpTCF("test/sv_rac_mod","test/sv_rac_mod","sv_rac/Decimal");
    }
    
    @Test
    public void Dzmz() {
        expectedRACExit = 1;
        helpTCF("test/Dzmz","test/Dzmz","Dzmz","-racJavaChecks");
    }



    @Test
    public void testbigint() {
        expectedExit = 0;
        helpTCF("test/racbigint","test/racbigint","bigint");
    }

    @Test
    public void testreal() {
        expectedExit = 0;
        helpTCF("test/racreal","test/racreal","real");
    }

    @Test
    public void demoStudent() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/student","test/demoStudent","ExecuteCStudent2","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testECU() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/ecudemo","test/ecurac","Test","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void purseCardTest() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purse","test/purse","CardTest");
    }

    @Test
    public void purseModTest() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purseMod","test/purseMod","CardTest");
    }

    @Test
    public void racTime() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Time.java","test/racTime","Time");
    }

    @Test
    public void racQueue() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Queue.java","test/racQueue","Queue");
    }

    @Test
    public void racAddng() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng/Add_InstanceStrategy.java","test/racaddng","Add_JML_Test","-cp","../OpenJML/bin-runtime"+z+"test/racaddng"+z+"test/racaddng/jmlunitng.jar","-jmltesting","-code-math=java","-spec-math=java");
    }

    @Test
    public void racAddng2() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng/Add_InstanceStrategy.java","test/racaddng2","Add_JML_Test","-cp","../OpenJML/bin-runtime"+z+"test/racaddng"+z+"test/racaddng/jmlunitng.jar","-jmltesting","-code-math=safe","-spec-math=bigint");
    }

    @Test
    public void racAddngall() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng","test/racaddngall","Add_JML_Test","-cp","../OpenJML/bin-runtime"+z+"test/racaddngall"+z+"test/racaddng"+z+"test/racaddng/jmlunitng.jar","-jmltesting","-code-math=java","-spec-math=java");
    }

    @Test
    public void racAddngall2() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racaddng","test/racaddngall2","Add_JML_Test","-cp","../OpenJML/bin-runtime"+z+"test/racaddngall"+z+"test/racaddng"+z+"test/racaddng/jmlunitng.jar","-jmltesting","-code-math=safe","-spec-math=bigint");
    }

    @Test
    public void racNoModel() {
        rac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racNoModel","test/racNoModel","NoModelTest","-racMissingModelFieldRepSource=skip");
    }

    @Test
    public void racMainActivity() {
        runrac = false; // FIXME: Don't try running executable until we supply some input
        //rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"test/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("test/racMainActivity","test/racMainActivity","MainActivity");
    }


    @Test
    public void racMainActivityMicro() {
        expectedExit = 0;
        helpTCF("test/racMainActivityMicro","test/racMainActivityMicro","CharAt");
    }

    @Test // FIXME - should we allow and compensate for \result in an \old environment
    public void racOld() {
        expectedExit = 1;
        runrac = false;
        helpTCF("test/racold","test/racold","ArrayExample");
    }
    
    @Test
    public void racHans4() {
    	expectedRACExit = 1;
    	rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata","-Dorg.jmlspecs.openjml.racexceptions=true","-Dorg.jmlspecs.openjml.racjavaassert=true","-Dorg.jmlspecs.openjml.racshowstack=false","StorageParameters"};
    	helpTCF("test/racHansStorage/StorageParameters.java","test/racHansStorage","StorageParameters","-racCheckAssumptions","-specspath=test/racHansStorage");
    	rac = null;
    }

    @Test
    public void racHans4a() {
    	expectedRACExit = 0;
    	rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata","-Dorg.jmlspecs.openjml.racexceptions=true","-Dorg.jmlspecs.openjml.racjavaassert=true","-Dorg.jmlspecs.openjml.racshowstack=false","StorageParameters"};
    	helpTCF("test/racHansStorage/StorageParameters.java","test/racHansStorageA","StorageParameters","-racCheckAssumptions","-specspath=test/racHansStorage","-nullableByDefault");
    	rac = null;
    }

    @Test
    public void racHans4b() {
        expectedRACExit = 1;
    	rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata","-Dorg.jmlspecs.openjml.racexceptions=true","-Dorg.jmlspecs.openjml.racjavaassert=true","-Dorg.jmlspecs.openjml.racshowstack=false","StorageParameters"};
    	helpTCF("test/racHansStorageB/StorageParameters.java","test/racHansStorageB","StorageParameters","-racCheckAssumptions","-specspath=test/racHansStorageB");
    	rac = null;
    }

    @Test // Bug in that some annotations had to be in the .java file, not the .jml, fixed
    public void racHans4c() {
        expectedRACExit = 0;
    	rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata","-Dorg.jmlspecs.openjml.racexceptions=true","-Dorg.jmlspecs.openjml.racjavaassert=true","-Dorg.jmlspecs.openjml.racshowstack=false","StorageParameters"};
    	helpTCF("test/racHansStorageC/StorageParameters.java","test/racHansStorageC","StorageParameters","-racCheckAssumptions","-specspath=test/racHansStorageC");
    	rac = null;
    }

    @Test  // Bug in that import statements must be in .java files, not .jml // FIXME - partially fixed - .jml imports are merged into .java imports
    public void racHans4d() {
        expectedRACExit = 0;
    	rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata","-Dorg.jmlspecs.openjml.racexceptions=true","-Dorg.jmlspecs.openjml.racjavaassert=true","-Dorg.jmlspecs.openjml.racshowstack=false","StorageParameters"};
    	helpTCF("test/racHansStorageD/StorageParameters.java","test/racHansStorageD","StorageParameters","-racCheckAssumptions","-specspath=test/racHansStorageD");
    	rac = null;
    }
    
    @Test
    public void racHansE() {
    	runrac = false;
    	helpTCF("test/hans/OpenJMLTest/src/javax/safetycritical/test/safelet/TckTestSafelet2.java",
    			"test/hans",
    			null,
    			"-cp","test/hans/OpenJMLTest/src"+z+"test/hans/icecapSDK/src",  //nFIXME - changed icecapSDK/bin to icecapSDK/src
    			"-rac",
    			"-specspath","test/hans/OpenJMLTest/specs",
    			"-racCheckAssumptions","-racJavaChecks","-showNotImplemented","-noInternalSpecs","-nullableByDefault"
    			);
    }

    @Test
    public void racHans2() {
        rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata"+z+"test/hans/OpenJMLTest/bin"+z+"test/hans/icecapSDK/src",null};

    	runrac = true;
    	helpTCF("test/racHans2/account",
    			"test/racHans2",
    			"account.AllTests",
    			"-cp","test/hans/OpenJMLTest/bin"+z+"test/hans/icecapSDK/src"+z+"test/racHans2",
    			//"-rac",
    			"-specspath","test/racHans2/specs",
    			"-racCheckAssumptions","-racJavaChecks","-showNotImplemented","-noInternalSpecs","-nullableByDefault"
    			);
    }

    @Test
    public void racNoGhostField() {
        expectedRACExit = 0;
        helpTCF("test/racNoGhostField","test/racNoGhostField","Magic","-jmltesting");
    }

    @Test
    public void gitbug524() {
        expectedRACExit = 0;
        helpTCF("test/gitbug524","test/gitbug524","Test"); 
    }

    @Test
    public void gitbug532() {
    	//runrac = false;
        expectedRACExit = 0;
        helpTCF("test/gitbug532","test/gitbug532","Big");
    }

    @Test
    public void gitbug532a() {
    	//runrac = false;
        expectedRACExit = 0;
        helpTCF("test/gitbug532a","test/gitbug532a","Big");
    }

    @Test
    public void gitbug533() {
    	//runrac = false;
        expectedRACExit = 0;
        helpTCF("test/gitbug533","test/gitbug533","TestSum","-racCheckAssumptions");
    }

    @Test
    public void gitbug533a() {
    	//runrac = false;
        expectedRACExit = 0;
        helpTCF("test/gitbug533a","test/gitbug533a","TestSum");
    }

    public void gitbug534() {
    	runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug534","test/gitbug534","S");
    }

    @Test
    public void gitbug536() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug536","test/gitbug536","Test536","-code-math=safe","-spec-math=safe");
    }

    @Test
    public void gitbug536a() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug536","test/gitbug536","Test536","-code-math=safe","-spec-math=bigint");
    }

    @Test
    public void gitbug542() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug542","test/gitbug542","Test542");
    }

    @Test
    public void gitbug542a() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug542","test/gitbug542a","Test542","-spec-math=java");
    }

    @Test
    public void gitbug542b() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug542","test/gitbug542b","Test542","-spec-math=safe");
    }

    @Test
    public void gitbug542c() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug542","test/gitbug542c","Test542","-spec-math=bigint");
    }

    @Test
    public void gitbug547() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug547","test/gitbug547","Test547");
    }

    @Test
    public void gitbug548rac() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug548rac","test/gitbug548rac","Test");
    }

    @Test
    public void gitbug548racB() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug548racB","test/gitbug548racB","Test");
    }

    @Test @Ignore // FIXME - Class encoding error in RAC
    public void gitbug584() {
        helpTCF("test/gitbug584","test/gitbug584","AClass");
    }

    @Test
    public void gitbug590() {
        runrac = false; // Expected compile error
        expectedExit = 1;
        helpTCF("test/gitbug590","test/gitbug590","Sequence");
    }

    @Test
    public void gitbug590a() {
        runrac = true;
        expectedRACExit = 0;
        expectedExit = 0;
        helpTCF("test/gitbug590a","test/gitbug590a","Sequence");
    }

    @Test
    public void gitbug599() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug599","test/gitbug599","Prime");
    }

    @Test
    public void gitbug627a() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug627a","test/gitbug627a","Test");
    }

    @Test
    public void gitbug688racA() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug688","test/gitbug688racA","DayTimeMain","-spec-math=bigint");
    }

    @Test
    public void gitbug688racB() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug688","test/gitbug688racB","DayTimeMain","-spec-math=safe");
    }

    @Test
    public void gitbug688racC() {
        runrac = true;
        expectedRACExit = 0;
        helpTCF("test/gitbug688","test/gitbug688racC","DayTimeMain","-spec-math=java");
    }

    @Test
    public void sfbug413() {
        expectedRACExit = 0;
        helpTCF("test/sfbug413","test/sfbug413","Main");
    }

    @Test
    public void sfbug402() {
        expectedRACExit = 0;
        runrac = false;
        helpTCF("test/sfbug402","test/sfbug402","Main");
    }

    @Test
    public void sfbug420() {
        expectedRACExit = 0;
        helpTCF("test/sfbug420","test/sfbug420","stack.StackImpl");
    }

    @Test
    public void sfbug396() {
        expectedRACExit = 0;
        runrac = false;
        helpTCF("test/sfbug396","test/sfbug396","Main");
    }

    @Test
    public void racRM1() {
        expectedRACExit = 0;
        helpTCF("test/racRM1","test/racRM1","Main","-code-math=java","-spec-math=java");
    }

    @Test
    public void racRM1a() {
        expectedRACExit = 0;
        helpTCF("test/racRM1","test/racRM1","Main","-code-math=safe","-spec-math=bigint");
    }

    @Test
    public void racRM2() {
        expectedRACExit = 0;
        helpTCF("test/racRM2","test/racRM2","Main","-code-math=java","-spec-math=java");
    }

    @Test
    public void racRM2a() {
        expectedRACExit = 0;
        helpTCF("test/racRM2","test/racRM2","Main","-code-math=safe","-spec-math=bigint");
    }
    
    @Test @Ignore // FIXME - RAC Not yet working for programs using string
    public void valuestrings() {
        expectedRACExit = 1;
        helpTCF("test/valuestrings","test/valuestrings","JmlStringTest");
    }


}
