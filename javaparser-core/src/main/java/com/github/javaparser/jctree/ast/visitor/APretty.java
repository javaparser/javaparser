package  com.github.javaparser.jctree.ast.visitor;

import com.github.javaparser.jctree.ast.*;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import java.io.*;

/* TODO - The JC add elements to the AST that are not AJC-
* Thus, all methods should test for their coresponding AJC type before printing the comments,
* So, a non-AJC element can be visited without raising and Exception, caused by bad type-casting.
* Other option: create a visitor that checks if there are a non-AJC node, and convert it.
*/
public class APretty extends Pretty {
   public APretty (Writer out, boolean sourceOutput) {
      super(out,sourceOutput);
   }
   public void visitTopLevel(JCCompilationUnit that) {
      if (((AJCCompilationUnit) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCCompilationUnit) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTopLevel(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitImport(JCImport that) {
      if (((AJCImport) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCImport) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitImport(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitClassDef(JCClassDecl that) {
      if (((AJCClassDecl) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCClassDecl) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitClassDef(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitMethodDef(JCMethodDecl that) {
      // Java adds a default constructor, which is not AJCMethodDecl. Adding test to this.

      if ( (that instanceof AJCMethodDecl) ) {
	 if ( ((AJCMethodDecl) that).hasComment() ) {
	    try {
	       println();
	       print("/*" + ((AJCMethodDecl) that).getComment() + "*/");
	    } catch (IOException e) {
	       System.err.println("Exception at line " +
		     Thread.currentThread().getStackTrace()[1].getLineNumber() +
		     ":" + 
		     e.getMessage());
	    } 
	 }

	 try {
	    super.visitMethodDef(that);
	 } catch(Exception e) {
	    System.err.println("Exception at line " +
		  Thread.currentThread().getStackTrace()[1].getLineNumber() +
		  ":" + 
		  e.getMessage() + ". Proceeding still...");
	 }
      }
   }

   public void visitVarDef(JCVariableDecl that) {
      if (((AJCVariableDecl) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCVariableDecl) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitVarDef(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitSkip(JCSkip that) {
      if (((AJCSkip) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCSkip) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitSkip(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitBlock(JCBlock that) {
      if (((AJCBlock) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCBlock) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitBlock(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitDoLoop(JCDoWhileLoop that) {
      if (((AJCDoWhileLoop) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCDoWhileLoop) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitDoLoop(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitWhileLoop(JCWhileLoop that) {
      if (((AJCWhileLoop) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCWhileLoop) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitWhileLoop(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitForLoop(JCForLoop that) {
      if (((AJCForLoop) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCForLoop) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitForLoop(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitForeachLoop(JCEnhancedForLoop that) {
      if (((AJCEnhancedForLoop) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCEnhancedForLoop) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitForeachLoop(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitLabelled(JCLabeledStatement that) {
      if (((AJCLabeledStatement) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCLabeledStatement) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitLabelled(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitSwitch(JCSwitch that) {
      if (((AJCSwitch) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCSwitch) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitSwitch(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitCase(JCCase that) {
      if (((AJCCase) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCCase) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitCase(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitSynchronized(JCSynchronized that) {
      if (((AJCSynchronized) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCSynchronized) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitSynchronized(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTry(JCTry that) {
      if (((AJCTry) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCTry) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTry(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitCatch(JCCatch that) {
      if (((AJCCatch) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCCatch) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitCatch(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitConditional(JCConditional that) {
      if (((AJCConditional) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCConditional) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitConditional(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitIf(JCIf that) {
      if (((AJCIf) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCIf) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitIf(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitExec(JCExpressionStatement that) {
      if (that instanceof AJCExpressionStatement) {
	 if (((AJCExpressionStatement) that).hasComment()) {
	    try {
	       println();
	       print("/*" + ((AJCExpressionStatement) that).getComment() + "*/");
	    } catch (IOException e) {
	       System.err.println("Exception at line " +
		     Thread.currentThread().getStackTrace()[1].getLineNumber() +
		     ":" + 
		     e.getMessage());
	    } 
	 }

	 try {
	    super.visitExec(that);
	 } catch(Exception e) {
	    System.err.println("Exception at line " +
		  Thread.currentThread().getStackTrace()[1].getLineNumber() +
		  ":" + 
		  e.getMessage() + ". Proceeding still...");
	 }
      }
   }

   public void visitBreak(JCBreak that) {
      if (((AJCBreak) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCBreak) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitBreak(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitContinue(JCContinue that) {
      if (((AJCContinue) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCContinue) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitContinue(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitReturn(JCReturn that) {
      if (((AJCReturn) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCReturn) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitReturn(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitThrow(JCThrow that) {
      if (((AJCThrow) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCThrow) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitThrow(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitAssert(JCAssert that) {
      if (((AJCAssert) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCAssert) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitAssert(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitApply(JCMethodInvocation that) {
      if (((AJCMethodInvocation) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCMethodInvocation) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitApply(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitNewClass(JCNewClass that) {
      if (((AJCNewClass) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCNewClass) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitNewClass(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitNewArray(JCNewArray that) {
      if (((AJCNewArray) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCNewArray) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitNewArray(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitParens(JCParens that) {
      if (((AJCParens) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCParens) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitParens(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitAssign(JCAssign that) {
      if (((AJCAssign) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCAssign) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitAssign(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitAssignop(JCAssignOp that) {
      if (((AJCAssignOp) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCAssignOp) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitAssignop(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitUnary(JCUnary that) {
      if (((AJCUnary) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCUnary) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitUnary(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitBinary(JCBinary that) {
      if (((AJCBinary) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCBinary) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitBinary(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeCast(JCTypeCast that) {
      if (((AJCTypeCast) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCTypeCast) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeCast(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeTest(JCInstanceOf that) {
      if (((AJCInstanceOf) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCInstanceOf) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeTest(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitIndexed(JCArrayAccess that) {
      if (((AJCArrayAccess) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCArrayAccess) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitIndexed(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitSelect(JCFieldAccess that) {
      if (((AJCFieldAccess) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCFieldAccess) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitSelect(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitIdent(JCIdent that) {
      if (((AJCIdent) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCIdent) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitIdent(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitLiteral(JCLiteral that) {
      if (((AJCLiteral) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCLiteral) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitLiteral(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeIdent(JCPrimitiveTypeTree that) {
      if (((AJCPrimitiveTypeTree) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCPrimitiveTypeTree) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeIdent(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeArray(JCArrayTypeTree that) {
      if (((AJCArrayTypeTree) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCArrayTypeTree) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeArray(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeApply(JCTypeApply that) {
      if (((AJCTypeApply) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCTypeApply) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeApply(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeUnion(JCTypeUnion that) {
      if (((AJCTypeUnion) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCTypeUnion) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeUnion(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeParameter(JCTypeParameter that) {
      if (((AJCTypeParameter) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCTypeParameter) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeParameter(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitWildcard(JCWildcard that) {
      if (((AJCWildcard) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCWildcard) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitWildcard(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitTypeBoundKind(TypeBoundKind that) {
      if (((ATypeBoundKind) that).hasComment()) {
         try {
            println();
            print("/*" + ((ATypeBoundKind) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitTypeBoundKind(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitAnnotation(JCAnnotation that) {
      if (((AJCAnnotation) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCAnnotation) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitAnnotation(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitModifiers(JCModifiers that) {
      if (((AJCModifiers) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCModifiers) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitModifiers(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitErroneous(JCErroneous that) {
      if (((AJCErroneous) that).hasComment()) {
         try {
            println();
            print("/*" + ((AJCErroneous) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitErroneous(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }

   public void visitLetExpr(LetExpr that) {
      if (((ALetExpr) that).hasComment()) {
         try {
            println();
            print("/*" + ((ALetExpr) that).getComment() + "*/");
         } catch (IOException e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage());
         } 
      }

      try {
         super.visitLetExpr(that);
      } catch(Exception e) {
            System.err.println("Exception at line " +
                               Thread.currentThread().getStackTrace()[1].getLineNumber() +
                               ":" + 
                               e.getMessage() + ". Proceeding still...");
      }
   }
}
