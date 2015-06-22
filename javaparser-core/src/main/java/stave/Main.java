/**
* STaVE - SyncTask Verifier
* Author: Pedro de Carvalho Gomes <pedrodcg@csc.kth.se>
*  
*/

package stave;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.DumpVisitor;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JavaCompiler.*;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.MemberEnter;
import com.sun.tools.javac.comp.Todo;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import java.util.ListIterator;
import java.io.*;
import java.net.URI;
import javax.tools.JavaFileManager;
import org.apache.commons.cli.*;
import stave.java.ast.*;
import stave.java.visitor.*;
import stave.javaparser.visitor.*;

public class Main {

   static private CommandLine cmd;

   static private boolean setOptions(String[] lcommand) {
 
      Options loptions = new Options();
      loptions.addOption( new Option("d",  "debug",   false,"print debug information (highly verbose)"));
      loptions.addOption( new Option("oj", "outjava", true, "output annotated Java program to file, and leave."));
      loptions.addOption( new Option("w",  "warning", false,"print warning messages"));

      CommandLineParser clparser = new PosixParser();
      try {
         cmd = clparser.parse( loptions, lcommand);
      } catch (org.apache.commons.cli.ParseException e) {
         // TODO - Check how to get this more precisely
         String mytoolcmd = "java -jar stave.jar";
         String myoptlist = " <options> <source files>";
         String myheader = "Input annotated Java or SynTask source, and output Coloured Petri Nets";
         String myfooter = "STaVe - SyncTask Verifier - http://www.csc.kth.se/~pedrodg/stave";

         HelpFormatter formatter = new HelpFormatter();
         // formatter.printUsage( new PrintWriter(System.out,true), 100, "java -jar stave.jar", loptions );
         // formatter.printHelp( mytoolcmd + myoptlist, myheader, loptions, myfooter, false);
         formatter.printHelp( mytoolcmd + myoptlist, loptions, false);
         return(false);
      }
      return(true);
   }

   private static void openAnnotatedJava() {
      // Create list with source code names
      @SuppressWarnings("unchecked")
      Vector<String> myfilelist = new Vector<String>( cmd.getArgList() );

      // Table that stores parsed compilation units
      Hashtable<String,CompilationUnit> myjpunitlist = new Hashtable<String,CompilationUnit>();

      // Generate AST with JavaParser
      for (Enumeration<String> e = myfilelist.elements(); e.hasMoreElements();) {
	 String mysource = "";
         CompilationUnit mycunit = null;

	 try {
	    // read filename
	    mysource = e.nextElement();

            // Compile it with java parser.
            mycunit = JavaParser.parse(new FileInputStream( mysource ));

            // Then fix the AST following the JC requirements
            ComplyToJCVisitor myfixervisitor = new ComplyToJCVisitor();
            mycunit = (CompilationUnit) myfixervisitor.visit( mycunit, new Integer(0));

	    // creates an input stream and parse it using Java Parser
	    myjpunitlist.put( mysource, mycunit);

	    if ( cmd.hasOption("d")) {
               // ASTDumpVisitor is verbose / DumpVisitor is clean
               ASTDumpVisitor myjpvisitor = new ASTDumpVisitor();
	       //DumpVisitor myjpvisitor = new DumpVisitor();
	       myjpvisitor.visit( myjpunitlist.get(mysource) ,null);
	       System.out.print(myjpvisitor.getSource());
	    }
	 } catch (com.github.javaparser.ParseException ex) {
	    System.out.println("Error: Parsing of Annotated Java file failed: " + mysource + ". Exiting...");
	    System.exit(1);
	 } catch (FileNotFoundException ex) {
	    System.out.println("Error: File not found: " + mysource + ". Exiting...");
	    System.exit(1);
	 }
      }

      //Building internals from Java Compiler
      Context mycontext = new Context();
      JavaCompiler myjcompiler = new JavaCompiler(mycontext);
      JavaFileManager myfilemanager = mycontext.get(JavaFileManager.class);
      // Phase that Javac may go to: Setting code generation
      myjcompiler.shouldStopPolicy = CompileState.GENERATE;

      // Table that stores the Java Compiler's ASTs
      List<JCCompilationUnit> ljctreelist = List.<JCCompilationUnit>nil();

      // Convert to Java Parser AST to JCTree AST's
      for (Enumeration<String> e = myjpunitlist.keys(); e.hasMoreElements();) {
         
	 // read filename
	 String mysource = e.nextElement();
         
         CompilationUnit myjpunit = myjpunitlist.get(mysource);

	 JavaParser2JCTree translator = new JavaParser2JCTree(mycontext);
	 AJCCompilationUnit myjctreeunit = (AJCCompilationUnit) translator.visit( myjpunit, myjpunit);

	 // Setting additional information for Javac: 
	 // - Source file. Otherwise it throws a NullPointerException
	 myjctreeunit.sourcefile = ((JavacFileManager)myfilemanager).getFileForInput(mysource);

	 // Storing in the list
	 ljctreelist = ljctreelist.append( myjctreeunit) ;

	 // Debug: Shows how the JCTree AST was generated. Output node types.
         // If one wants the clean output, should use the JCtree.tree.Pretty instead.
	 if ( cmd.hasOption("d")) {
	    try {
	       Writer mystdout  = new OutputStreamWriter(System.out);
	       (new PrintAstVisitor(mystdout,true)).visitTopLevel(myjctreeunit);
	       mystdout.flush();
	    } catch (Exception z) {}
	 }
      }
      
      /*
      * The following are the phases of the Oracle's Java compiler
      * The output of one is the input of another, and calls can be nested.
      */

      // Enter (phase I): starting to build symtable
      Enter myenter = Enter.instance(mycontext);
      myenter.main( ljctreelist);
      // Enter (phase II): Finishing to build symtable
      /* MemberEnter mymemberenter = MemberEnter.instance(mycontext);
         mymemberenter.visitTopLevel(myjctreeunit); */

      // Get the todo list generated by Enter phase
      // From now on, the output of a phase is the input of the other.
      Todo mytodo = Todo.instance(mycontext);
 
      // atrribute: type-checking, name resolution, constant folding
      // flow: deadcode elimination
      // desugar: removes synctactic sugar: inner classes, class literals, assertions, foreachs 
      myjcompiler.desugar(myjcompiler.flow(myjcompiler.attribute( mytodo)));

      // generate: produce bytecode or source code. Erases the whole AST
      // myjcompiler.generate(myjcompiler.desugar(myjcompiler.flow(myjcompiler.attribute( mytodo))));

      // Prints the Java program to output files and leave
      if ( cmd.hasOption("oj")) {
	 for(ListIterator<JCCompilationUnit> i = ljctreelist.listIterator(); i.hasNext();) {
	    JCCompilationUnit myjctreeunit = i.next();
	    try {
	       Writer myoutputfile;

	       if ( cmd.getOptionValue("oj") == null) {
		  myoutputfile = new  FileWriter(FileDescriptor.out);
	       } else {
		  myoutputfile = new  FileWriter( cmd.getOptionValue("oj") );
	       } 

	       (new APretty(myoutputfile,true)).visitTopLevel(myjctreeunit);
	       myoutputfile.flush();

	    } catch (Exception e) {
               // TODO - Check what to report in case of error.
	    }
	 }
	 return;
      }
   }

   public static void main(String argv[]) {
      if (setOptions(argv)) openAnnotatedJava();
   }
}
