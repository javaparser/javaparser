package org.jmlspecs.openjmltest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Strings;
import org.junit.Before;
import org.junit.BeforeClass;

import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/** This is a base class for unit test files that exercise the RAC.
 * It inherits from JmlTestCase the diagnostic collector implementation
 * and the (optional) collection of System.out and System.err.  It 
 * implements as well the mechanisms for running RAC via programmatic
 * calls to openjml and then executing the resulting program.
 * 
 * @author David R. Cok
 *
 */
public abstract class RacBase extends JmlTestCase {
	
	public final static String OpenJMLDemoPath = "../../OpenJMLDemo";
	
    protected String testspecpath1 = "$A"+z+"$B";
    protected String testspecpath;
    protected int expectedExit = 0; // Expected result of compiler
    protected int expectedRACExit = 0; // Expected result of RACed program
    protected int expectedNotes; // Number of messages to ignore (e.g. uninteresting compiler warnings)
    protected boolean jdkrac = false; // Set to true to do external system tests of RAC (emulating outside of JUnit)
    protected boolean continueAnyway = false; // If true, attempt to run the program despite compiler warnings or errors
    
    protected String expected_compile = "expected-compile";
    protected String expected_run = "expected-run";

    /** These are the default command-line arguments for running the RACed
     * program.  The first argument is the java executable; the null argument
     * is replaced by the class name of the class containing the main method.     
     * */
    protected String[] defrac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    /** These are actual command-line arguments, if they are set differently
     * by a subclass.
     */
    protected String[] rac; // initialized in subclasses
    

    @BeforeClass
    public static void mktempdirectory() {
    	File f = new File("testdata");
    	if (!f.exists()) {
    		f.mkdir();
    	}
    }
    
    /** Derived classes can initialize
     * testspecpath1 - the specspath to use
     * <BR>jdkrac - default is false; if true, adjusts the classpath???
     * <BR>rac - the command-line to run the raced program; default is the contents of defrac
     * <BR>
     * After this call, if desired, modify
     * <BR>print - if true, prints out errors as encountered, for test debugging (and disables failing the JUnit test if the error mismatches)
     * <BR>expectedExit - the expected exit code from running openjml
     * <BR>expectedRacExit - the expected exit code from running the RACed program
     * <BR>expectedErrors - the expected number of errors from openjml (typically and by default 0)
     */
    @Override
    @Before
    public void setUp() throws Exception {
        //System.out.println("Using " + jdk);
        
        // Use the default specs path for tests
        testspecpath = testspecpath1;
        // Define a new collector that filters out the notes
        collector = new FilteredDiagnosticCollector<JavaFileObject>(false);
        super.setUp();
        
        // Setup the options
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-d", "testdata"); // This is where the output program goes
        main.addOptions("-rac","-racJavaChecks","-racCheckAssumptions");
        if (jdkrac) {
            String sy = Options.instance(context).get(Strings.eclipseProjectLocation);
            if (sy == null) {
                fail("The OpenJML project location should be set using -D" + Strings.eclipseProjectLocation + "=...");
            } else if (!new File(sy).exists()) {
                fail("The OpenJML project location set using -D" + Strings.eclipseProjectLocation + " to " + sy + " does not exist");
            } else {
                main.addOptions("-classpath",sy+"/testdata"+z+sy+"/jdkbin"+z+sy+"/bin");
            }
        }
        main.addOptions("-showNotImplemented");
        main.addOptions("-no-purityCheck"); // System specs have a lot of purity errors, so turn this off for now
        main.addOptions("-no-internalSpecs"); // Faster with this option; should work either way
        main.addOptions("-no-racShowSource");
        specs = JmlSpecs.instance(context);
        expectedExit = 0;
        expectedRACExit = 0;
        expectedNotes = 2; // Two lines to ignore
        print = false;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }
    
    public static String macstring = "Exception in thread \"main\" ";

    
    /** This method does the running of a RAC test for tests that supply with body
     * of a file as a String.
     * No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param classname The fully-qualified classname for the test class
     * @param compilationUnitText the compilation unit text which will be put in a mock file
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCX(String classname, String compilationUnitText, Object... list) {

        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        StreamGobbler out=null,err=null;
        boolean isMac = System.getProperty("os.name").contains("Mac");
        try {
            ListBuffer<JavaFileObject> files = new ListBuffer<JavaFileObject>();
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,compilationUnitText);
            files.append(f);
            for (JavaFileObject ff: mockFiles) {
                if (ff.toString().endsWith(".java")) files.append(ff);
            }

            Log.instance(context).useSource(files.first());
            int ex = main.compile(new String[]{}, null, context, files.toList(), null).exitCode;
            
            if (print) printDiagnostics();
            int observedMessages = collector.getDiagnostics().size() - expectedNotes;
            if (observedMessages < 0) observedMessages = 0;

            for (int i=0; i<observedMessages; i++) {
                int k = 2*i + 2*expectedNotes;
                if (k >= list.length) {
                    if (!print) printDiagnostics();
                    fail("More diagnostics than expected");
                }
                String s = noSource(collector.getDiagnostics().get(i));
                if (s.startsWith(macstring) && isMac) s = s.substring(macstring.length());
                assertEquals("Message " + i, list[k].toString(), s);
                assertEquals("Message " + i, ((Integer)list[k+1]).intValue(), collector.getDiagnostics().get(i).getColumnNumber());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            if (ex != 0 && !continueAnyway) return;
            
            if (rac == null) rac = defrac;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);
            
            out = new StreamGobbler(p.getInputStream());
            err = new StreamGobbler(p.getErrorStream());
            out.start();
            err.start();
            if (timeout(p,10000)) { // 10 second timeout
                fail("Process did not complete within the timeout period");
            }
            
            int i = observedMessages*2;
            if (print) {
                String data = out.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                data = err.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            String data = out.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String line: lines) {
                    if (i < list.length) assertEquals("Output line " + i, list[i], line);
                    i++;
                }
            }
            data = err.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String line: lines) {
                	if (isMac && line.startsWith(macstring) && i < list.length && !line.equals(list[i])) line = line.substring(macstring.length());
                    if (i < list.length) assertEquals("Output line " + i, list[i], line);
                    i++;
                }
                if (isMac && i < list.length && list[i].equals(macstring)) i++;
            }

            if (i != list.length && !print) { // if print, then we already printed
                printDiagnostics();
            }
            if (i> list.length) fail("More output than specified: " + i + " vs. " + list.length + " lines");
            if (i< list.length) fail("Less output than specified: " + i + " vs. " + list.length + " lines");
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print) printDiagnostics();
            if (!print && !noExtraPrinting) {
                if (out != null) {
                    String[] lines = out.input().split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                if (err != null) {
                    String[] lines = err.input().split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            throw e;
        } finally {
//            if (r != null) 
//                try { r.close(); } 
//                catch (java.io.IOException e) { 
//                    // Give up if there is an exception
//                }
//            if (rerr != null) 
//                try { rerr.close(); } 
//                catch (java.io.IOException e) {
//                    // Give up if there is an exception
//                }
        }
    }
    
    // The following is for tests based on files

    protected boolean runrac = true;
    
    /** The command-line to use to run RACed programs - note the inclusion of the
     * RAC-compiled JDK library classes ahead of the regular Java library classes
     * in the boot class path. (This may not work on all platforms)
     */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};
    
    /** Call this as a setup routine, followed by RacBase.setUp for file based tests */
    public void setUpForFiles() throws Exception {
        rac = sysrac;
        jdkrac = true;
        runrac = true;
    }


    /** This method does the running of a RAC test that is based in an external file.  No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param dirname The directory containing the test sources, a relative path
     * from the project folder
     * @param mainClassname The fully-qualified classname for the test class (where main is)
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCF(String dirname, String outputdir, String mainClassname, String ... opts) {
        boolean print = false;
        StreamGobbler out=null,err=null;
        try {
            String actCompile = outputdir + "/actual-compile";
            String actRun = outputdir + "/actual-run";
            new File(outputdir).mkdirs();
            new File(actCompile).delete();
            new File(actRun).delete();
            List<String> args = new LinkedList<String>();
            //args.add("-no-jml");
            args.add("-d");
            args.add("testdata");
            args.add("-rac");
            args.add("-no-purityCheck");
            args.add("-code-math=java");
            args.add("-spec-math=bigint");
            if (new File(dirname).isDirectory()) args.add("-dir");
            args.add(dirname);
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String compdiffs = "";
            if (new File(outputdir + "/" + expected_compile).exists()) {
            	compdiffs = outputCompare.compareFiles(outputdir + "/" + expected_compile, actCompile);
        		if (compdiffs == null) {
        			new File(actCompile).delete();
        		} 
        	} else {
            	for (String file: new File(outputdir).list()) {
            		if (!file.contains("expected-compile")) continue;
            		compdiffs = outputCompare.compareFiles(outputdir + "/" + file, actCompile);
            		if (compdiffs == null) {
            			new File(actCompile).delete();
            			break;
            		}
            	}
            }
            if (compdiffs != null) {
                if (compdiffs.isEmpty()) {
                    compdiffs = ("No expected output file for compiler output");
                    System.out.println(compdiffs);
                } else {
                    System.out.println(compdiffs);
                    //  fail("Files differ: " + compdiffs);
                }
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

            if (runrac) {
                if (rac == null) rac = defrac;
                rac[rac.length-1] = mainClassname;
                Process p = Runtime.getRuntime().exec(rac);

                out = new StreamGobbler(p.getInputStream());
                err = new StreamGobbler(p.getErrorStream());
                out.start();
                err.start();
                if (timeout(p,10000)) { // 10 second timeout
                    fail("Process did not complete within the timeout period");
                }
                String output = out.input().replaceAll("@[0-9abcdef]+", "@########");
                ex = p.exitValue();
                output = "OUT:" + eol + output + eol + "ERR:" + eol + err.input();
                if (print) System.out.println(output);
                String diffs = "";
                for (String file: new File(outputdir).list()) {
                    if (!file.contains("expected-run")) continue;
                    diffs = outputCompare.compareText(outputdir + "/" + file,output);
                    if (diffs == null) break;
                }
                if (diffs != null) {
                    BufferedWriter b = new BufferedWriter(new FileWriter(actRun));
                    b.write(output);
                    b.close();
                }
                if (ex != expectedRACExit) fail("Execution ended with exit code " + ex + " " + output);
                if (diffs != null) {
                    if (diffs.isEmpty()) {
                        fail("No expected output file for runtime output");
                    } else {
                        System.out.println(diffs);
                        fail("Unexpected output: " + diffs);
                    }
                }
            }
            if (compdiffs != null) fail("Files differ: " + compdiffs);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }
}
