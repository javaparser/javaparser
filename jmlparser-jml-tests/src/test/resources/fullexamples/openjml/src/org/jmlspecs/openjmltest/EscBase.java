package org.jmlspecs.openjmltest;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.TimeUnit;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjmltest.OutputCompare.*;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.rules.Timeout;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


public abstract class EscBase extends JmlTestCase {
    
	public static final String OpenJMLDemoPath = "../../OpenJMLDemo";
	
    @Rule public TestName testname = new TestName();
    @Rule public Timeout timeout = new Timeout(10, TimeUnit.MINUTES); // limit on entire test, not on each proof attempt
    
    protected static boolean runLongTests = System.getProperty("SKIPLONGTESTS") == null;

    static {
        if (!runLongTests) System.out.println("Skipping long-running tests");
    }

    static public java.util.List<String> solvers = java.util.Arrays.asList(new String[]{ 
            "z3_4_3", 
//            "z3_4_7", 
 //           "z3_4_5", 
 //           "z3_4_6", 
 //           "z3_4_3_1", 
//          "z3_4_4", 
//            "cvc4",
            //"yices2",
 //             "yices", 
 //            "simplify" 
            });
        
    static public java.util.List<String> solversWithNull;
    		{
    			solversWithNull = new LinkedList<String>();
    			solversWithNull.add(null);
    			solversWithNull.addAll(solvers);
    		}
        
//    static public java.util.List<String[]> minQuants = java.util.Arrays.asList(new String[][]{ 
//            new String[]{"-minQuant"}, 
//            new String[]{"-no-minQuant"}, 
//            });
        
    /** The parameters must be a String[] and a String */
    @Parameters
    static public Collection<String[]> parameters() {
        return solversOnly();
    }
    
    static public Collection<String[]> solversOnly() {
        return makeParameters(solvers);
    }
    
    public String getMethodName(int i) {
    	return (new RuntimeException()).fillInStackTrace().getStackTrace()[i+1].getMethodName();
    }
    
//    public static final String[] minQuantOptions = new String[]{"-no-minQuant","-minQuant"};
    
    static public  Collection<String[]> solvers(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            data.add(new String[]{s});
        }
        return data;
    }

    static public  Collection<String[]> optionsAndSolvers(String[] options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
        	for (String opts: options) {
        		data.add(new String[]{opts,s});
        	}
        }
        return data;
    }

    
    static public  Collection<String[]> makeParameters(java.util.List<String> options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            for (String option: options) {
                data.add(new String[]{option,s});
            }
        }
        return data;
    }

    static public  Collection<String[]> makeParameters(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }

    static public  Collection<String[]> makeParameters(String... solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }
    
    static public void addOptionsToArgs(String options, java.util.List<String> args) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	for (String o: options.split(",")) if (!o.isEmpty()) args.add(o);
            } else {
            	for (String o: options.split(" ")) if (!o.isEmpty()) args.add(o);
            }
        }
    }
    
    public void addOptions(String options) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	main.addOptions(options.split(","));
            } else {
            	main.addOptions(options.split(","));
            }
        }
    }
    

    /** options is a comma- or space-separated list of options to be added */
    protected String options;
    protected String solver;
    protected boolean captureOutput = false;
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBase(String options, String solver) {
        this.options = options;
        this.solver = solver;
    }
    
//    public void printDiagnostics() {
//        System.out.println("SOLVER: " + solver + " " + options);
//        super.printDiagnostics();
//    }

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath1 = "$A"+z+"$B";
    protected static String testspecpath;
    
    // Set this field to the expected exit value. 
    // 0: only static checking errors, not parsing or type errors
    // 1: parsing or type errors
    // -1: don't check the exit value
    protected int expectedExit = 0;
    protected boolean noAssociatedDeclaration;
    protected String[] args;
//    protected String openJmlPropertiesDir = "../OpenJML"; 

    @Override
    public void setUp() throws Exception {
        if (captureOutput) collectOutput(true);
        testspecpath = testspecpath1;
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-command","esc");
        main.addOptions("-keys","NOARITH");
        main.addOptions("-escExitInfo","-no-purityCheck");
//        main.addOptions("-timeout=300"); // seconds
        main.addOptions("-jmltesting");
        main.addUncheckedOption("openjml.defaultProver=z3_4");
        addOptions(options);
        if (solver != null) main.addOptions(JmlOption.PROVER.optionName(),solver);
        specs = JmlSpecs.instance(context);
        expectedExit = 0;
        noAssociatedDeclaration = false;
        ignoreNotes = false;
        print = false;
        args = new String[]{};
        MethodProverSMT.benchmarkName = 
                (this.getClass() + "." + testname.getMethodName()).replace("[0]", "").substring(6);
    }

    public void escOnFiles(String sourceDirname, String outDir, String ... opts) {
    	boolean print = false;
    	try {
    		java.util.List<String> args = setupForFiles(sourceDirname, outDir, opts);
    		String actCompile = outDir + "/actual";
    		new File(actCompile).delete();
    		PrintWriter pw = new PrintWriter(actCompile);
    		int ex = -1;
    		try {
    			ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
    		} finally {
    			pw.close();
    		}

    		String diffs = outputCompare.compareFiles(outDir + "/expected", actCompile);
    		int n = 0;
    		while (diffs != null) {
    			n++;
    			String name = outDir + "/expected" + n;
    			if (!new File(name).exists()) break;
    			diffs = outputCompare.compareFiles(name, actCompile);
    		}
    		if (diffs != null) {
    		    System.out.println("TEST DIFFERENCES: " + testname.getMethodName());
    			System.out.println(diffs);
    			fail("Files differ: " + diffs);
    		}  
    		if (expectedExit != -1 && ex != expectedExit) fail("Compile ended with exit code " + ex);
    		new File(actCompile).delete();

    	} catch (Exception e) {
    		e.printStackTrace(System.out);
    		fail("Exception thrown while processing test: " + e);
    	} catch (AssertionError e) {
    		throw e;
    	} finally {
    		// Should close open objects
    	}
    }

    public void escOnFile(String sourceFilename, String outDir, String ... opts) {
    	boolean print = false;
    	try {
    		new File(outDir).mkdirs();
    		java.util.List<String> args = setupForFiles(sourceFilename, outDir, opts);
    		String actCompile = outDir + "/actual";
    		new File(actCompile).delete();
    		PrintWriter pw = new PrintWriter(actCompile);
    		int ex = -1;
    		try {
    			ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
    		} finally {
    			pw.close();
    		}

    		String diffs = outputCompare.compareFiles(outDir + "/expected", actCompile);
    		int n = 0;
    		while (diffs != null) {
    			n++;
    			String name = outDir + "/expected" + n;
    			if (!new File(name).exists()) break;
    			diffs = outputCompare.compareFiles(name, actCompile);
    		}
    		if (diffs != null) {
    		    System.out.println("TEST DIFFERENCES: " + testname.getMethodName());
    			System.out.println(diffs);
    			fail("Files differ: " + diffs);
    		}  
    		if (expectedExit != -1 && ex != expectedExit) fail("Compile ended with exit code " + ex);
    		new File(actCompile).delete();

    	} catch (Exception e) {
    		e.printStackTrace(System.out);
    		fail("Exception thrown while processing test: " + e);
    	} catch (AssertionError e) {
    		throw e;
    	} finally {
    		// Should close open objects
    	}
    }

    public java.util.List<String> setupForFiles(String sourceDirOrFilename, String outDir, String ... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-esc");
        args.add("-no-purityCheck");
        args.add("-jmltesting");
        args.add("-progress");
        args.add("-timeout=300");
        args.add("-code-math=java");
        if (!new File(sourceDirOrFilename).isFile()) args.add("-dir");
        args.add(sourceDirOrFilename);
        if (solver != null) args.add("-prover="+solver);
        addOptionsToArgs(options,args);        
        args.addAll(Arrays.asList(opts));
        return args;
    }
    
    
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
        captureOutput = false;
        MethodProverSMT.benchmarkName = null;
    }

    
    protected void helpTCX2(String classname, String s, String classname2, String s2, Object... list) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            String filename2 = classname2.replace(".","/")+".java";
            JavaFileObject f2 = new TestJavaFileObject(filename2,s2);
            Log.instance(context).useSource(f);
            helpTCXB(List.of(f,f2),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCX(String classname, String s, Object... list) {
        try {
            String filename = classname.replace(".","/") +".java";  // FIXME - I think this string should be prefixed with $A/ 
            JavaFileObject f = new TestJavaFileObject(filename,s);
            Log.instance(context).useSource(f);
            helpTCXB(List.of(f),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCXB(List<JavaFileObject> files, Object... list) {
        try {
            for (JavaFileObject f: mockFiles) files = files.append(f);
            
            int ex = main.compile(args, null, context, files, null).exitCode;
            if (captureOutput) collectOutput(false);
            
            if (print) printDiagnostics();
            outputCompare.compareResults(list,collector);
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

        } catch (Exception e) {
        	printDiagnostics();
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw e;
        }
    }
    
    protected OneOf oneof(Object ... list) { return new OneOf(list); }
    protected AnyOrder anyorder(Object ... list) { return new AnyOrder(list); }
    protected Optional optional(Object ... list) { return new Optional(list); }
    protected Seq seq(Object ... list) { return new Seq(list); }
    

//    protected boolean comparePair(Object[] list, int i, int j, boolean issueErrors) {
//        int col = ((Integer)list[i+1]).intValue();
//        if (collector.getDiagnostics().size() <= j) {
//            failureLocation = j;
//            failureString = null;
//        	return false;
//        }
//        String act = noSource(collector.getDiagnostics().get(j));
//        String exp = null;
//        if (list[i] != null) exp = list[i].toString().replace("$SPECS", specsdir);
//        long actualColumn = -1;
//        if (!exp.equals(act) 
//                && !exp.replace('\\','/').equals(act.replace('\\','/'))) {
//            failureLocation = j;
//            failureString = list[i].toString();
//            if (issueErrors) assertEquals("Error " + j, list[i], noSource(collector.getDiagnostics().get(j)));
//            return false;
//        } else if (col != (actualColumn = Math.abs(collector.getDiagnostics().get(j).getColumnNumber()))) {
//            failureLocation = j;
//            failureString = null;
//            failureCol = col;
//            if (issueErrors) assertEquals("Error " + j, col, actualColumn);
//            return false;
//        } else {
//            return true;
//        }
//    }
//
//    /** Compares actual diagnostics against the given list of expected results */
//    protected int compareResults(Object[] list) {
//    	return compareResults(list,0,false);
//    }
//
//    /** Compares actual diagnostics, beginning at position j, to given list. The
//     * returned result is either the initial value of j, if no match was made,
//     * or the value of j advanced over all matching items. If optional is false,
//     * then error messages are printed if no match is found.
//     */
//    protected int compareResults(Object list, int j, boolean optional) {
//    	return compareResults(new Object[]{list}, j, optional);
//    }
//    protected int compareResults(Object[] list, int j, boolean optional) {
//        int i = 0;
//        while (i < list.length) {
//            if (list[i] == null) { i+=2; continue; }
//            if (!(list[i] instanceof Special)) {
//                int col = ((Integer)list[i+1]).intValue();
//                if (col < 0) {
//                    // allowed to be optional
//                    if (j >= collector.getDiagnostics().size()) {
//                        // OK - just skip
//                    } else if (list[i].equals(noSource(collector.getDiagnostics().get(j))) &&
//                            -col == Math.abs(collector.getDiagnostics().get(j).getColumnNumber())) {
//                        j++;
//                    } else {
//                        // Not equal and the expected error is optional so just skip
//                    }
//                } else {
//                    if (noAssociatedDeclaration && list[i].toString().contains("Associated declaration")) {
//                        // OK - skip
//                    } else {
//                        if (j < collector.getDiagnostics().size()) {
//                        	if (!comparePair(list,i,j, !optional)) {
//                                if (!optional) {
//                                    assertEquals("Error " + j, col, collector.getDiagnostics().get(j).getColumnNumber());
//                                	assertEquals("Error " + j, list[i], noSource(collector.getDiagnostics().get(j)));
//                                }
//                            }
//                        }
//                        j++;
//                    }
//                }
//                i += 2;
//            } else if (list[i] instanceof AnyOrder) {
//                j = compareAnyOrder(((AnyOrder)list[i]).list, j, optional);
//                ++i;
//            } else if (list[i] instanceof OneOf) {
//                j = compareOneOf(((OneOf)list[i]).list, j, optional);
//                ++i;
//            } else if (list[i] instanceof Optional) {
//                j = compareOptional(((Optional)list[i]).list, j);
//                ++i;
//            } else if (list[i] instanceof Seq) {
//                j = compareResults(((Seq)list[i]).list, j, optional);
//                ++i;
//            }
//        }
//        return j;
//    }
//    
//    protected int failureLocation;
//    protected String failureString;
//    protected int failureCol;
//    
//    protected int compareOptional(Object[] list, int j) {
//        int i = 0;
//        int jj = j;
//        while (i < list.length) {
//            if (!comparePair(list,i,j, false)) {
//                // Comparison failed - failureLocation set
//                return jj;
//            }
//            i += 2;
//            j++;
//        }
//        return j;
//    }
//
//    protected int compareOneOf(Object[] list, int j, boolean optional) {
//        // None of lists[i] may be null or empty
//        int i = 0;
//        int jj = j;
//        int latestFailure = -2;
//        String latestString = null;
//        int latestCol = 0;
//        while (i < list.length) {
//            int jjj = compareResults(list[i],j,true);
//            if (jjj > j) {
//                // Matched
//                return jjj;
//            }
//            i++;
//            if (failureLocation > latestFailure) {
//                latestFailure = failureLocation;
//                latestString = failureString;
//                latestCol = failureCol;
//            }
//        }
//        failureLocation = latestFailure;
//        if (!optional) { // None matched;
//        	assertEquals("Error " + failureLocation, latestString, noSource(collector.getDiagnostics().get(failureLocation)));
//        	assertEquals("Error " + failureLocation, latestCol, collector.getDiagnostics().get(failureLocation).getColumnNumber());
//        }
//        return jj;
//    }
//
//
//    protected int compareAnyOrder(Object[] list, int j, boolean optional) {
//        // None of lists[i] may be null or empty
//        boolean[] used = new boolean[list.length];
//        for (int i=0; i<used.length; ++i) used[i] = false;
//        
//        int latestFailure = -2;
//        String latestString = null;
//        int latestCol = 0;
//        int toMatch = list.length;
//        more: while (toMatch > 0) {
//            for (int i = 0; i < list.length; ++i) {
//                if (used[i]) continue;
//                int jjj = compareResults(list[i],j,true);
//                if (jjj > j) {
//                    // Matched
//                    j = jjj;
//                    used[i] = true;
//                    toMatch--;
//                    continue more;
//                } else {
//                    if (failureLocation > latestFailure) {
//                        latestFailure = failureLocation;
//                        latestString = failureString;
//                        latestCol = failureCol;
//                    }
//                }
//            }
//            // No options match
//            break;
//        }
//        if (toMatch > 0) {
//            failureLocation = latestFailure;
//            // None matched;
//            if (failureLocation >= collector.getDiagnostics().size()) {
//            	fail("Less output than expected");
//            } else {
//            	assertEquals("Error " + failureLocation, latestString, noSource(collector.getDiagnostics().get(failureLocation)));
//            	assertEquals("Error " + failureLocation, latestCol, collector.getDiagnostics().get(failureLocation).getColumnNumber());
//            }
//        }
//        return j;
//    }


}
