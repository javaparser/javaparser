package org.jmlspecs.openjmltest;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.TestName;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;


/** This class provides basic functionality for the JUnit tests for OpenJML.
 * It is expected that actual JUnit test suites will derive from this class.
 * <P>
 * It creates a DiagnosticListener that collects all of the error and warning
 * messages from executing the test.  This class does not capture other messages
 * (e.g. straight to std out), but some subclasses do.  The captured error and 
 * warning messages are compared against test supplied text - for both the text
 * of the message, which includes file name and line number - and the column 
 * number.
 * 
 * @author David Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public abstract class JmlTestCase {

    // This value is for running tests, so we can presume the current directory is .../OpenJML/OpenJMLTest
    public final static String specsdir = System.getenv("SPECSDIR") != null ? System.getenv("SPECSDIR") : Paths.get("../../Specs").toAbsolutePath().toString();
    public final static String streamLine = "9"; // This line number is present in many test oracle files, but changes as edits are made to Stream.jml
    
    static protected boolean isWindows = System.getProperty("os.name").contains("Wind");

    static protected String projLocation = System.getProperty("openjml.eclipseProjectLocation");
    
    static protected String root = new File(".").getAbsoluteFile().getParentFile().getParentFile().getParent();
    
    protected boolean ignoreNotes = false; // FIXME - set but does not appear to be used anywhere
    
    // An object holding routines for comparing output with oracle output
    public OutputCompare outputCompare = new OutputCompare();

    /** This is here so we can get the name of a test, using name.getMethodName() */
    @Rule public TestName name = new TestName();
    
    /** The java executable */
    // TODO: This is going to use the external setting for java, rather than
    // the current environment within Eclipse
    protected String jdk = System.getProperty("java.home") + "/bin/java";

    /** A purposefully short abbreviation for the system path separator
     * ( ; or : )
     */
    static final public String z = java.io.File.pathSeparator;
    
    /** Cached value of the end of line character string */
    static final public String eol = System.getProperty("line.separator");

    /** A Diagnostic listener that can report all the collected diagnostics */
    static public interface DiagnosticListenerX<S> extends DiagnosticListener<S> {
        public List<Diagnostic<? extends S>> getDiagnostics();
    }

    final static public class FilteredDiagnosticCollector<S> implements DiagnosticListenerX<S> {
        /** Constructs a diagnostic listener that collects all of the diagnostics,
         * with the ability to filter out the notes.
         * @param filtered if true, no notes (only errors and warnings) are collected
         */
        public FilteredDiagnosticCollector(boolean filtered) {
            this.filtered = filtered;
        }
        
        /** If true, no notes are collected. */
        boolean filtered;
        
        /** The collection (in order) of diagnostics heard so far. */
        private java.util.List<Diagnostic<? extends S>> diagnostics =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

        /** The method called by the system when there is a diagnostic to report. */
        public void report(Diagnostic<? extends S> diagnostic) {
            diagnostic.getClass(); // null check
            if (!filtered || diagnostic.getKind() != Diagnostic.Kind.NOTE)
                diagnostics.add(diagnostic);
        }

        /**
         * Gets a list view of diagnostics collected by this object.
         *
         * @return a list view of diagnostics
         */
        public java.util.List<Diagnostic<? extends S>> getDiagnostics() {
            return Collections.unmodifiableList(diagnostics);
        }
    }
    
    public static class StreamGobbler extends Thread
    {
        private InputStream is;
        private StringBuffer input = new StringBuffer();
        
        public StreamGobbler(InputStream is) {
            this.is = is;
        }
        
        public String input() {
            return input.toString();
        }
        
        public void run() {
            try {
                char[] cbuf = new char[10000];
                InputStreamReader isr = new InputStreamReader(is);
                BufferedReader br = new BufferedReader(isr);
                int n;
                while ((n = br.read(cbuf)) != -1) {
                    input.append(cbuf,0,n);
                }
            } catch (IOException ioe) {
                ioe.printStackTrace();  
            }
        }
    }
    
    private static class InterruptScheduler extends TimerTask {
        Thread target = null;
        
        public InterruptScheduler(Thread target) {
            this.target = target;
        }
        
        @Override
        public void run() {
            target.interrupt();
        }
    }
    
    public static boolean timeout(Process p, long milliseconds) {
        // Set a timer to interrupt the process if it does not return within the timeout period
        Timer timer = new Timer();
        timer.schedule(new InterruptScheduler(Thread.currentThread()), new Date(System.currentTimeMillis()+milliseconds));
        try {
            p.waitFor();
        } catch (InterruptedException e) {
            // Stop the process from running
            p.destroy();
            return true;
        } finally {
            // Stop the timer
            timer.cancel();
        }
        return false;
    }

    // References to various tools needed in testing
    protected Context context;
    protected Main main;
    protected Options options;
    protected JmlSpecs specs; // initialized in derived classes
    protected LinkedList<JavaFileObject> mockFiles;
    
    /** Normally false, but set to true in tests of the test harness itself, to
     * avoid printing out diagnostic messages when a test fails.
     */
    public boolean noExtraPrinting = false;

    /** Set this to true in a test to print out more detailed information about
     * what the test is doing (as a debugging aid).
     */
    public boolean print = false;
    
    /** Set this to true (in the setUp for a test, before calling super.setUp)
     * if you want diagnostics to be printed as they occur, rather than being
     * collected.
     */
    public boolean noCollectDiagnostics = false;
    
    /** A collector for all of the diagnostic messages */
    protected DiagnosticListenerX<JavaFileObject> collector = new FilteredDiagnosticCollector<JavaFileObject>(false);
    
    /** Set this to true (for an individual test) if you want debugging information */
    public boolean jmldebug = false;
    
    /** This does some setup, but most of it has to be left to the derived classes because we have to
     * set the options before we register most of the JML tools.
     */
    @Before
    public void setUp() throws Exception {
        main = new Main("",new PrintWriter(System.out, true),!noCollectDiagnostics?collector:null, null,
        		"-properties", "../OpenJML/openjml.properties");
        context = main.context();
        options = Options.instance(context);
        if (jmldebug) {  // FIXME - this is not the right way to set debugging
            Utils.instance(context).jmlverbose = Utils.JMLDEBUG; 
            main.addOptions("-jmlverbose", "4");
        }
        print = false;
        mockFiles = new LinkedList<JavaFileObject>();
        Log.instance(context).multipleErrors = true;
        //System.out.println("JUnit: Testing " + getName());
    }

    /** Nulls out all the references visible in this class */
    @After
    public void tearDown() throws Exception {
        context = null;
        main = null;
        collector = null;
        options = null;
        specs = null;
    }


    /** Prints a diagnostic as it is in an error or warning message, but without
     * any source line.  This is how dd.toString() used to behave, but in OpenJDK
     * build 55, toString also included the source information.  So we need to 
     * wrap dd in this call (or change all of the tests).
     * @param dd the diagnostic
     * @return
     */
    static protected String noSource(Diagnostic<? extends JavaFileObject> dd) {
        return dd instanceof JCDiagnostic ? noSource((JCDiagnostic)dd) : dd.toString();
    }

    
    /** Prints out the errors collected by the diagnostic listener */
    public void printDiagnostics() {
        System.out.println("DIAGNOSTICS " + collector.getDiagnostics().size() + " " + name.getMethodName());
        for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
            long line = dd.getLineNumber();
            long start = dd.getStartPosition();
            long pos = dd.getPosition();
            long end = dd.getEndPosition();
            long col = dd.getColumnNumber();
            System.out.println(noSource(dd) + " line=" + line + " col=" + col + " pos=" + pos + " start=" + start + " end=" + end);
        }
    }

    /** Checks that all of the collected diagnostic messages match the data supplied
     * in the arguments.
     * @param messages an array of expected messages that are checked against the actual messages
     * @param cols an array of expected column numbers that are checked against the actual diagnostics
     */
    public void checkMessages(/*@ non_null */String[] messages, /*@ non_null */int[] cols) {
        List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
        if (print || (!noExtraPrinting && messages.length != diags.size())) printDiagnostics();
        assertEquals("Saw wrong number of errors ",messages.length,diags.size());
        assertEquals("Saw wrong number of columns ",cols.length,diags.size());
        for (int i = 0; i<diags.size(); ++i) {
            assertEquals("Message for item " + i,messages[i],noSource(diags.get(i)));
            assertEquals("Column number for item " + i,cols[i],diags.get(i).getColumnNumber()); // Column number is 1-based
        }
    }

    /** Checks that all of the collected messages match the data supplied
     * in the arguments.
     * @param a a sequence of expected values, alternating between error message and column numbers
     */
    public void checkMessages(/*@ nonnullelements */Object ... a) {
        try {
            assertEquals("Wrong number of messages seen",a.length,2*collector.getDiagnostics().size());
            List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
            if (print || (!noExtraPrinting && 2*diags.size() != a.length)) printDiagnostics();
            assertEquals("Saw wrong number of errors ",a.length,2*diags.size());
            for (int i = 0; i<diags.size(); ++i) {
                assertEquals("Message for item " + i,a[2*i].toString(),noSource(diags.get(i)));
                assertEquals("Column number for item " + i,((Integer)a[2*i+1]).intValue(),diags.get(i).getColumnNumber()); // Column number is 1-based
            }
        } catch (AssertionError ae) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw ae;
        }
    }
    
    /** Checks that there are no diagnostic messages */
    public void checkMessages() {
        if (print || (!noExtraPrinting && 0 != 2*collector.getDiagnostics().size())) printDiagnostics();
        assertEquals("Saw wrong number of messages ",0,collector.getDiagnostics().size());
    }

    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param content the String constituting the content of the pseudo-file
     */
    protected void addMockFile(/*@ non_null */ String filename, /*@ non_null */String content) {
        try {
            addMockFile(filename,new TestJavaFileObject(new URI("file:///" + filename),content));
        } catch (Exception e) {
            fail("Exception in creating a URI: " + e);
        }
    }

    protected ByteArrayOutputStream berr;
    protected ByteArrayOutputStream bout;
    protected PrintStream savederr;
    protected PrintStream savedout;
    protected String actualErr;
    protected String actualOut;

    /** Manages the capturing of output to System.out and System.err; call with argument=true to start
     * capturing; all with the argument=false to stop capturing, at which point with Strings actualOut 
     * and actualErr will contain the collected output (access them through output() and errorOutput() ).
     */
    public void collectOutput(boolean collect) {
        if (collect) {
            actualOut = null;
            actualErr = null;
            savederr = System.err;
            savedout = System.out;
            System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
            System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
        } else {
            System.err.flush();
            System.out.flush();
            actualErr = berr.toString();
            actualOut = bout.toString();
            berr = null;
            bout = null;
            System.setErr(savederr);
            System.setOut(savedout);
        }
    }
    
    /** Returns the standard-out output; valid once collectOutput(false) has been called. */
    public String output() { return actualOut; }
    /** Returns the standard-err output; valid once collectOutput(false) has been called. */
    public String errorOutput() { return actualErr; }


    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param file the JavaFileObject to be associated with this name
     */
    protected void addMockFile(String filename, JavaFileObject file) {
        if (filename.endsWith(".java")) mockFiles.add(file);
        specs.addMockFile(filename,file);
    }
    
    /** Used to add a pseudo file to the command-line.
     * @param filename the name of the file, including leading directory components 
     * @param file the JavaFileObject to be associated with this name
     */
    protected void addMockJavaFile(String filename, /*@ non_null */String content) {
        try {
            addMockFile(filename,new TestJavaFileObject(new URI("file:///" + filename),content));
        } catch (Exception e) {
            fail("Exception in creating a URI: " + e);
        }
    }
    
    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param file the JavaFileObject to be associated with this name
     */
    protected void addMockJavaFile(String filename, JavaFileObject file) {
        mockFiles.add(file);
    }

    
    /** Returns the diagnostic message without source location information */
    static String noSource(JCDiagnostic dd) {
        return dd.noSource();
    }

    public static String doReplacements(String s) {
        return s.replace("$ROOT",JmlTestCase.root).replace("$SPECS",specsdir).replace("$STRL", JmlTestCase.streamLine);
    }

}


