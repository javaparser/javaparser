package org.jmlspecs.openjmltest;
import java.net.URI;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

import static org.junit.Assert.*;


/** This is a base class for all tests that parse and typecheck a
 * test string of source code.  Mock files are created (or real ones used)
 * to simulate a set of input files.  Any diagnostics are captured with
 * a listener and compared with the expected diagnostics.
 * 
 * FIXME - should we be checking the out and err outputs as well?
 * 
 * @author David R. Cok
 *
 */
public abstract class TCBase extends JmlTestCase {

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath1 = "$A"+z+"$B"+z+"../OpenJML/bin-runtime";
    protected String testspecpath;
    protected int expectedExit = -1;
    protected boolean useSystemSpecs = false;

    @Override
    public void setUp() throws Exception {
        testspecpath = testspecpath1;
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        main.addOptions("-specspath",   testspecpath + (!useSystemSpecs ? "" : (z + "$SY") ));
        main.addOptions("-sourcepath",   testspecpath);
        main.addOptions("-classpath",   "../OpenJML/bin-runtime");
        if (!useSystemSpecs) main.addOptions("-no-internalSpecs");
        main.addOptions(JmlOption.PURITYCHECK.optionName()+"=false");

        JmlAttr.instance(context);
        JmlEnter.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        specs = JmlSpecs.instance(context);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

    public void helpFailure(String failureMessage, String s, Object ... list) {
        noExtraPrinting = true;
        boolean failed = false;
        try {
            helpTC(s,list);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }

    public void helpTC(String s, Object ... list) {
        helpTCX(null,s,list);
    }

    public void helpTCF(String filename,String s, Object ... list) {
        helpTCX(filename,s,list);
    }

    public void helpTCX(String filename, String s, Object[] list) {
        try {
            JavaFileObject f = new TestJavaFileObject(filename,s);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            //comp.compile(files,List.<String>nil(),null);
            int ex = main.compile(new String[]{ "-Xlint:unchecked" }, null, context, files, null).exitCode;
            
            if (print) JmlSpecs.instance(context).printDatabase();
            if (print) printDiagnostics();
            int i=0;
            int k = 0;
            Object p1,p2,p3,p4;
            for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
                if (k >= list.length) break;
                String expected = doReplacements(((String)list[k++]));
                assertEquals("Message " + i + " mismatch",expected,noSource(dd));
                p1 = (k < list.length && list[k] instanceof Integer) ? list[k++] : null;
                p2 = (k < list.length && list[k] instanceof Integer) ? list[k++] : null;
                p3 = (k < list.length && list[k] instanceof Integer) ? list[k++] : null;
                p4 = (k < list.length && list[k] instanceof Integer) ? list[k++] : null;
                if (p4 != null) {
                    assertEquals("Column for message " + i,((Integer)p1).intValue(),dd.getColumnNumber());
                    assertEquals("Start for message " + i,((Integer)p2).intValue(),dd.getStartPosition());
                    assertEquals("Position for message " + i,((Integer)p3).intValue(),dd.getPosition());
                    assertEquals("End for message " + i,((Integer)p4).intValue(),dd.getEndPosition());
                } else if (p1 != null) {
                    assertEquals("Column for message " + i,((Integer)p1).intValue(),dd.getColumnNumber());
                } else {
                    fail("No positions given for message " + i);
                }
                i++;
            }
            if (k < list.length) fail("Fewer errors observed (" + collector.getDiagnostics().size() + ") than expected");
            if (i < collector.getDiagnostics().size()) fail("More errors observed (" + collector.getDiagnostics().size() + ") than expected (" + i + ")");
            if (expectedExit == -1) expectedExit = list.length == 0?0:1;
            assertEquals("Wrong exit code",expectedExit, ex);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw e;
        }
    }

//    /** Used to add a pseudo file to the file system. Note that for testing, a 
//     * typical filename given here might be #B/A.java, where #B denotes a 
//     * mock directory on the specification path
//     * @param filename the name of the file, including leading directory components 
//     * @param content the String constituting the content of the pseudo-file
//     */
//    protected void addMockFile(/*@ non_null */ String filename, /*@ non_null */String content) {
//        try {
//            addMockFile(filename,new TestJavaFileObject(new URI("file:///" + filename),content));
//        } catch (Exception e) {
//            fail("Exception in creating a URI: " + e);
//        }
//    }
//
//    /** Used to add a pseudo file to the file system. Note that for testing, a 
//     * typical filename given here might be #B/A.java, where #B denotes a 
//     * mock directory on the specification path
//     * @param filename the name of the file, including leading directory components 
//     * @param file the JavaFileObject to be associated with this name
//     */
//    protected void addMockFile(String filename, JavaFileObject file) {
//        specs.addMockFile(filename,file);
//    }
//



}

