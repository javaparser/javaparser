package org.jmlspecs.openjmltest.testcases;


import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;
import org.jmlspecs.openjmltest.RacBase;
import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsRac extends RacBase {

    /** Enables or disables this suite of tests */
    static private boolean dotests = true;  // Change this to enable/disable dynamic tests
    
    /** If true, then a progress message is printed as each test is executed.*/
    private static boolean verbose = false;

    @Parameters
    static public  Collection<String[]> datax() {
        if (!dotests) return new ArrayList<String[]>(0);
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (File f: findAllFiles()) {
            data.add(new String[]{ f.getName()});
        }
        return data;
    }

    /** The name of the class to be tested (which is also the name of the test)
     * when the suite mode is used. This is defined simply to enable debugging.
     */
    /*@ non_null*/
    private String classname;
    
    /** We use SpecsBase as a test case, with a name and its own runTest, to
     * execute the test on a given class name.
     * @param classname the fully qualified class to test
     */
    public SpecsRac(String classname) {
        this.classname = classname;
    }


    @Override
    public void setUp() throws Exception {
        super.setUp();
        // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
        JmlOption.setOption(context,JmlOption.PURITYCHECK,false);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false; // true = various debugging output
    }
    
    /** Set to true if errors are found in any test in checkFiles */
    protected boolean foundErrors;
    
    /** This test tests the file that is named as classname by the constructor */
    @Test
    public void testSpecificationFile() {
    	expectedExit = 0;
    	ignoreNotes = true;
    	String subdir = "testspecs" + "/" + classname;
    	String testname = null;
        for (File f: new File(subdir).listFiles()) {
        	if (f.getName().startsWith("Test")) {
        		testname = f.getName().replace(".java","");
        		break;
        	}
        }
    	helpTCF(subdir,subdir,testname);
    }
    
    static public java.util.List<File> findAllFiles() {
        File dir = new File("testspecs");
        java.util.List<File> classes = new ArrayList<>();
        for (File f: dir.listFiles()) if (f.isDirectory()) classes.add(f);
        System.out.println(classes.size() + " system specification classes found for rac testing");
        return classes;
    }
    

}
