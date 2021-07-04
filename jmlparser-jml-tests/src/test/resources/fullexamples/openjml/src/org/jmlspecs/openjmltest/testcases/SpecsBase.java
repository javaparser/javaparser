package org.jmlspecs.openjmltest.testcases;


import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;
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

/** This is the parent class for classes that simply test whether the spec file 
 * for a JDK class parses without error.  There are two methods of creating
 * these tests implemented here.
 * <P>
 * One is to create a TestSuite, and dynamically add to it an individual test
 * for each class found.  That construction has to be done statically.  It has
 * the advantage that each test appears in the JUnit list of tests and marked
 * as successful or not.  The individual tests can be rerun from the JUnit
 * test runner, but the suite as a whole cannot.  The suite can be run as a
 * Run Configuration.  Another advantage is that the tests can
 * be canceled while in progress.
 * <P>
 * A second implementation, currently disabled, has SpecsBase consisting of
 * just one test, that loops through all the classes being tested.  A disadvantage
 * is that one cannot cancel the tests while in progress and they do not appear
 * in the JUnit listing.  They can also be run from the RunConfiguration.  To
 * enable this mode, comment out the suite() and runTest() methods.
 * 
 * <P>
 * Alternatively, you can create explicit tests for individual system classes.
 * The template is the following:
 * 
 *<PRE>
    public void testFile() {
        checkClass("<fully-qualified-type-name>");
    }
   </PRE>
 * or
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { <fully-qualified-type-name> f; }"
                );
    }
   </PRE>
 *
 *For generic classes (with one type argument) write
 *<PRE>
    public void testFile() {
        checkClassGeneric("<fully-qualified-type-name>");
    }
   </PRE>
 * or
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { <fully-qualified-type-name><?> f; }"
                );
    }
   </PRE>
 *
 * Note also that no errors are reported if there is no specification file or 
 * the class path is such that the spec file is not found.
 * 
 * @author David Cok
 *
 */
// Note - this does not test spec files that are hidden by a later version
//   you need to rerun Eclipse with a different JDK and correspondingly different
//   specifications path.  You can do this with separate Run Configurations.

// At one point in development, running these tests would cause later tests in
// the JUnit sequence to fail, when they would not fail otherwise.  Before that
// problem could be solved, it disappeared, so its cause and resolution are
// unknown.  For now we will leave these tests in, but beware that this was once
// the case and may crop up again in the future.

// Since these tests are a bit time-consuming (about 2 min right now) and will be
// more so as more spec files are added, you can turn them off with the dotests
// flag.

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsBase extends TCBase {

    /** Enables or disables this suite of tests */
    static private boolean dotests = true;  // Change this to enable/disable dynamic tests
    
    /** If true, then a progress message is printed as each test is executed.*/
    private static boolean verbose = false;

    @Parameters
    static public  Collection<String[]> datax() {
        if (!dotests) return new ArrayList<String[]>(0);
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (String f: findAllFiles(null)) {
            data.add(new String[]{ f});
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
    public SpecsBase(String classname) {
        this.classname = classname;
    }

    java.util.List<String> jars;
    String jarString;

    @Override
    public void setUp() throws Exception {
        useSystemSpecs = true;
        super.setUp();
        jars = java.nio.file.Files.list(Paths.get("../OpenJMLTest/libs")).map(Path::toString).collect(java.util.stream.Collectors.toList());
        jars.add(0,"../OpenJML/bin-runtime"); // prepend
        jarString = String.join(File.pathSeparator,jars);
        main.addOptions("-classpath",jarString);
        // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
        JmlOption.setOption(context,JmlOption.PURITYCHECK,false);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false; // true = various debugging output
    }
    
    /** Set to true if errors are found in any test in checkFiles */
    protected boolean foundErrors;
    
    /** Helper method that executes a test 
     * 
     * @param filename name to use for the pseudo source file
     * @param s the code for the pseudo source file
     * @param testClass class being tested, for output only
     */
    //@ modifies foundErrors;
    public void helpTCFile(String filename, String s, String testClass) {
        try {
            JavaFileObject f = new TestJavaFileObject(filename,s);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            String cp1 = "/Users/davidcok/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar";
            //String cp2 = "libs/hamcrest-junit-2.0.0.0.jar:libs/java-hamcrest-2.0.0.0.jar";
            int ex = main.compile(new String[]{"-cp",cp1 + ":" + jarString}, null, context, files, null).exitCode;
            if (print) JmlSpecs.instance(context).printDatabase();
            int expected = expectedExit;
            if (expected == -1) expected = collector.getDiagnostics().size() == 0 ? 0 : 1;
            if (ex != expected) {
                System.out.println("Unexpected return code for "  + testClass + " actual: " + ex + " expected: " + expected);
                foundErrors = true;
            }
            if (collector.getDiagnostics().size() != 0) {
                System.out.println("ERRORS FOUND " + testClass);
                foundErrors = true;
                printDiagnostics();
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + testClass + " " + e);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw e;
        }
        assertTrue("Found errors checking specs for " + testClass, !foundErrors);
    }

    /** This test tests the file that is named as classname by the constructor */
    @Test
    public void testSpecificationFile() {
        foundErrors = false;
        int n = counts.get(classname);
        if (verbose) System.out.println("JUnit SpecsBase: " + classname + " " + n);
        if (n < typeargs.length) checkClass(classname, n);
        else {
            assertTrue("Not implemented for " + n + " + generic arguments: " + classname,false);
        }

        assertTrue("Errors found",!foundErrors);
    }
    
    /** Finds all classes that have library specification files.
     */
    static public SortedSet<String> findAllFiles(/*@ nullable*/ JmlSpecs specs) {
        System.out.println("JRE version " + System.getProperty("java.version"));
        try {
            if (specs == null) {
                Main main = new Main();
                Context context = main.context();
                specs = JmlSpecs.instance(context);
                specs.setSpecsPath("$SY");
            }
        } catch (IOException e) {
            e.printStackTrace();
            fail("Exception in findAllFiles");
        }
        java.util.List<Dir> dirs = specs.getSpecsPath();
        assertTrue ("Null specs path",dirs != null); 
        assertTrue ("No specs path",dirs.size() != 0); 
        
        SortedSet<String> classes = new TreeSet<String>(); 
        for (Dir dir: dirs) {
            File d = new File(dir.toString());
            classes.addAll(findAllFiles(d, dir.toString()));
        }
        classes.removeAll(donttest);
        System.out.println(classes.size() + " system specification classes found");
        return classes;
    }
    
    /** Set of classes (fully qualified, dot-separated names) that should not
     * be tested.
     */
    static Set<String> donttest = new HashSet<String>();
    static {
        donttest.add("org.junit.Assert"); // (FIXME) Turn this off because the test coes not find the junit library 
    }
    
    static java.util.HashMap<String,Integer> counts = new java.util.HashMap<>();
    
    
    /** Creates a list of all the files (of any suffix), interpreted as fully-qualified Java class 
     * names when the root prefix is removed,
     * recursively found underneath the given directory
     * @param d the directory in which to search
     * @param root the prefix of the path to ignore
     * @return list of dot-separated class names for which files were found
     */
    static public java.util.List<String> findAllFiles(File d, String root) {
        String[] files = d.list();
        java.util.List<String> list = new ArrayList<String>();
        if (files == null) return list;
        for (String s: files) {
            if (s.charAt(0) == '.') continue;
            File f = new File(d,s);
            if (f.isDirectory()) {
                list.addAll(findAllFiles(f, root));
            } else {
                String qualifiedName = f.toString().substring(root.length()+1);
                int p = qualifiedName.lastIndexOf('.');
                String baseName = qualifiedName.substring(0,p).replace(File.separatorChar,'.');
                list.add(baseName);
                int numArgs = countTypeArgs(f,baseName);
                Integer nn = counts.get(baseName);
                if (nn == null || numArgs > nn) counts.put(baseName, numArgs);
            }
        }
        return list;
    }
    
    public static int countTypeArgs(File f, String baseName) {
        try {
            // This is a imprecise method to count the number of type arguments, but so for I have not
            // found any .jml files for which it fails. If the number is wrong and non-zero, the test will fail,
            // but if wrong and 0 it may not.
            java.util.List<String> lines = java.nio.file.Files.readAllLines(f.toPath(), java.nio.charset.Charset.defaultCharset());
            StringBuffer sb = new StringBuffer();
            for (String line: lines) sb.append(line);
            String all = sb.toString();
            int k = baseName.lastIndexOf('.');
            String tail = baseName.substring(k+1);
            k = all.indexOf(tail + "<");
            int n = 0;
            if (k >= 0) {
                n = 1;
                k += (tail + "<").length();
                int depth = 0;
                while (depth >= 0) {
                    char c = all.charAt(k);
                    if (c == '<') depth++;
                    if (c == ',' && depth == 0) n++;
                    if (c == '>') depth--;
                    k++;
                }
            }
            return n;
        } catch (Exception e) {
            assertTrue("Failed to find number of generic type arguments", false);
            return 0;
        }    
    }
    
    String[] typeargs = { "", "<?>", "<?,?>" , "<?,?,?>" };

    /** Does a test on the given fully qualified,
     * dot-separated class name with n generic type arguments
     * 
     * @param className the name of the class to test
     */
    //@ modifies foundErrors;
    public void checkClass(String className, int n) {
        String program = "public class AJDK { "+ className + typeargs[n] +" o; }";
        // Do these  because the classes are not public
        if (className.equals("java.lang.AbstractStringBuilder")) program = "package java.lang; " + program;
        if (className.equals("java.lang.StringCoding")) program = "package java.lang; " + program;
        helpTCFile("AJDK.java",program,className);
    }
        
    // FIXME - the above test template does not seem to trigger all the
    // modifier checking in attribute testing.

    /** Use this to test the specs for a specific file. Enable it by
     * adding an @Test as an annotation. */
    
    // @Test
    public void testFileTemp() {
        checkClass("java.util.LinkedList", 1);
    }

}
