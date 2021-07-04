package org.jmlspecs.openjmltest;

import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.junit.runners.Parameterized.Parameters;

public class StrongarmBase extends EscBase {

    public StrongarmBase(String options, String solver) {
	super(options, solver);
    }
    
    //-infer -infer-debug  -progress -verbose 

    public java.util.List<String> setupForFiles(String sourceDirname, String outDir, String... opts) {
	new File(outDir).mkdirs();
	java.util.List<String> args = new LinkedList<String>();
	//args.add("-infer");
	//args.add("-infer-debug");
	
	args.add("-infer-persist=jml");
	args.add("-infer");
	//args.add("-verbose");
	//args.add("-progress");
	if (new File(sourceDirname).isDirectory())
	    args.add("-dir");
	args.add(sourceDirname);
	if (solver != null)
	    args.add("-prover=" + solver);
	addOptionsToArgs(options, args);
	args.addAll(Arrays.asList(opts));
	return args;
    }

    // TODO - should really reafactor this so we don't run the tests twice...
    @Parameters
    static public Collection<String[]> parameters() {
	return new ArrayList<String[]>();
    }

    public int doStrongarm(List<String> argsl, String actCompile) {

	try {
	    
	    String[] args = argsl.toArray(new String[0]);
	    String classpath = System.getProperty("java.class.path");
	    String javaHome = System.getProperty("java.home");
	    String javaBin = javaHome + File.separator + "bin" + File.separator + "java";

	    String[] baseArgs = new String[] { javaBin, "-Dopenjml.eclipseSpecsProjectLocation=../../Specs", "-cp",
		    classpath, "org.jmlspecs.openjml.Main" };

	    String[] processArgs = new String[baseArgs.length + args.length];

	    System.arraycopy(baseArgs, 0, processArgs, 0, baseArgs.length);
	    System.arraycopy(args, 0, processArgs, baseArgs.length, args.length);

	    ProcessBuilder builder = new ProcessBuilder(processArgs);

	    Process process = builder.start();

	    BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
	    PrintWriter pw = new PrintWriter(actCompile);

	    String line;

	    List<String> jml = new ArrayList<String>();

	    StringBuffer output = new StringBuffer();

	    while ((line = reader.readLine()) != null) {
		System.out.println(line);
		pw.write(line + "\n");
	    }

	    return process.waitFor();

	} catch (Exception e) {
	    e.printStackTrace();
	}

	return 1;
    }

    public void onFile(String sourceName, String outDir, String... opts) {
	boolean print = false;
	try {

	    java.util.List<String> args = setupForFiles(sourceName, outDir, opts);

	    String actCompile = outDir + "/actual";
	    String expectedCompile = outDir + "/expected";

	    String[] clz = (FileSystems.getDefault().getPath(sourceName).getFileName().toString().split("\\."));

	    String expectedSpec = outDir + "/" + clz[0] + "_expected.jml";
	    String actSpec = outDir + "/" + clz[0] + ".jml";

	    if(new File(actCompile).exists()){
		new File(actCompile).delete();		    
	    }
	    
	    if(new File(actSpec).exists()){
		new File(actSpec).delete();		    
	    }
	    
	    
	    // before we do anything, if the expected spec doesn't exist, that
	    // means we
	    // are generating it.
	    if (new File(expectedSpec).exists() == false) {

		if (new File(actSpec).exists()) {
		    new File(actSpec).delete();
		}

		int ex = doStrongarm(args, actCompile);
		if (ex == expectedExit) {
		    System.out.println(String.format("Generated Expected Spec: %s from %s", expectedSpec, actSpec));
		    new File(actSpec).renameTo(new File(expectedSpec));
		} else {
		    System.out.println("Failed to generate expected spec.");
		}

		return;

	    }

	    int ex = doStrongarm(args, actCompile);
	    
	    if (ex != expectedExit)
		fail("Compile ended with exit code " + ex);

	    // if we care about the compile output, do the comparison
	    if (new File(expectedCompile).exists()) {
		String diffs = outputCompare.compareFiles(expectedCompile, actCompile);
		
		if (diffs != null) {
		    
		    System.out.println(diffs);
		    fail("Files differ: " + diffs);
		}
		
		new File(actCompile).delete();

	    }

	    if (new File(expectedSpec).exists()) {

		String diffs = outputCompare.compareFiles(expectedSpec, actSpec);
		
		if (diffs != null) {

		    System.out.println(diffs);
		    fail("Files differ: " + diffs);
		}
		
		new File(actSpec).delete();

	    }

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
