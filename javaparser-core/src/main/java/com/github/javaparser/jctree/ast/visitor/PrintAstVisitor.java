package  com.github.javaparser.jctree.ast.visitor;

import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import java.io.Writer;

public class PrintAstVisitor extends Pretty {
   public PrintAstVisitor (Writer out, boolean sourceOutput) {
      super(out,sourceOutput);
   }
   public void visitTopLevel(JCCompilationUnit that) { try { print("JCCompilationUnit:"); } catch (Exception e) {} super.visitTopLevel(that); } 
   public void visitImport(JCImport that) { try { print("JCImport:"); } catch (Exception e) {} super.visitImport(that); } 
   public void visitClassDef(JCClassDecl that) { try { print("JCClassDecl:"); } catch (Exception e) {} super.visitClassDef(that); } 
   public void visitMethodDef(JCMethodDecl that) { try { print("JCMethodDecl:"); } catch (Exception e) {} super.visitMethodDef(that); } 
   public void visitVarDef(JCVariableDecl that) { try { print("JCVariableDecl:"); } catch (Exception e) {} super.visitVarDef(that); } 
   public void visitSkip(JCSkip that) { try { print("JCSkip:"); } catch (Exception e) {} super.visitSkip(that); } 
   public void visitBlock(JCBlock that) { try { print("JCBlock:"); } catch (Exception e) {} super.visitBlock(that); } 
   public void visitDoLoop(JCDoWhileLoop that) { try { print("JCDoWhileLoop:"); } catch (Exception e) {} super.visitDoLoop(that); } 
   public void visitWhileLoop(JCWhileLoop that) { try { print("JCWhileLoop:"); } catch (Exception e) {} super.visitWhileLoop(that); } 
   public void visitForLoop(JCForLoop that) { try { print("JCForLoop:"); } catch (Exception e) {} super.visitForLoop(that); } 
   public void visitForeachLoop(JCEnhancedForLoop that) { try { print("JCEnhancedForLoop:"); } catch (Exception e) {} super.visitForeachLoop(that); } 
   public void visitLabelled(JCLabeledStatement that) { try { print("JCLabeledStatement:"); } catch (Exception e) {} super.visitLabelled(that); } 
   public void visitSwitch(JCSwitch that) { try { print("JCSwitch:"); } catch (Exception e) {} super.visitSwitch(that); } 
   public void visitCase(JCCase that) { try { print("JCCase:"); } catch (Exception e) {} super.visitCase(that); } 
   public void visitSynchronized(JCSynchronized that) { try { print("JCSynchronized:"); } catch (Exception e) {} super.visitSynchronized(that); } 
   public void visitTry(JCTry that) { try { print("JCTry:"); } catch (Exception e) {} super.visitTry(that); } 
   public void visitCatch(JCCatch that) { try { print("JCCatch:"); } catch (Exception e) {} super.visitCatch(that); } 
   public void visitConditional(JCConditional that) { try { print("JCConditional:"); } catch (Exception e) {} super.visitConditional(that); } 
   public void visitIf(JCIf that) { try { print("JCIf:"); } catch (Exception e) {} super.visitIf(that); } 
   public void visitExec(JCExpressionStatement that) { try { print("JCExpressionStatement:"); } catch (Exception e) {} super.visitExec(that); } 
   public void visitBreak(JCBreak that) { try { print("JCBreak:"); } catch (Exception e) {} super.visitBreak(that); } 
   public void visitContinue(JCContinue that) { try { print("JCContinue:"); } catch (Exception e) {} super.visitContinue(that); } 
   public void visitReturn(JCReturn that) { try { print("JCReturn:"); } catch (Exception e) {} super.visitReturn(that); } 
   public void visitThrow(JCThrow that) { try { print("JCThrow:"); } catch (Exception e) {} super.visitThrow(that); } 
   public void visitAssert(JCAssert that) { try { print("JCAssert:"); } catch (Exception e) {} super.visitAssert(that); } 
   public void visitApply(JCMethodInvocation that) { try { print("JCMethodInvocation:"); } catch (Exception e) {} super.visitApply(that); } 
   public void visitNewClass(JCNewClass that) { try { print("JCNewClass:"); } catch (Exception e) {} super.visitNewClass(that); } 
   public void visitNewArray(JCNewArray that) { try { print("JCNewArray:"); } catch (Exception e) {} super.visitNewArray(that); } 
   public void visitParens(JCParens that) { try { print("JCParens:"); } catch (Exception e) {} super.visitParens(that); } 
   public void visitAssign(JCAssign that) { try { print("JCAssign:"); } catch (Exception e) {} super.visitAssign(that); } 
   public void visitAssignop(JCAssignOp that) { try { print("JCAssignOp:"); } catch (Exception e) {} super.visitAssignop(that); } 
   public void visitUnary(JCUnary that) { try { print("JCUnary:"); } catch (Exception e) {} super.visitUnary(that); } 
   public void visitBinary(JCBinary that) { try { print("JCBinary:"); } catch (Exception e) {} super.visitBinary(that); } 
   public void visitTypeCast(JCTypeCast that) { try { print("JCTypeCast:"); } catch (Exception e) {} super.visitTypeCast(that); } 
   public void visitTypeTest(JCInstanceOf that) { try { print("JCInstanceOf:"); } catch (Exception e) {} super.visitTypeTest(that); } 
   public void visitIndexed(JCArrayAccess that) { try { print("JCArrayAccess:"); } catch (Exception e) {} super.visitIndexed(that); } 
   public void visitSelect(JCFieldAccess that) { try { print("JCFieldAccess:"); } catch (Exception e) {} super.visitSelect(that); } 
   public void visitIdent(JCIdent that) { try { print("JCIdent:"); } catch (Exception e) {} super.visitIdent(that); } 
   public void visitLiteral(JCLiteral that) { try { print("JCLiteral:"); } catch (Exception e) {} super.visitLiteral(that); } 
   public void visitTypeIdent(JCPrimitiveTypeTree that) { try { print("JCPrimitiveTypeTree:"); } catch (Exception e) {} super.visitTypeIdent(that); } 
   public void visitTypeArray(JCArrayTypeTree that) { try { print("JCArrayTypeTree:"); } catch (Exception e) {} super.visitTypeArray(that); } 
   public void visitTypeApply(JCTypeApply that) { try { print("JCTypeApply:"); } catch (Exception e) {} super.visitTypeApply(that); } 
   public void visitTypeUnion(JCTypeUnion that) { try { print("JCTypeUnion:"); } catch (Exception e) {} super.visitTypeUnion(that); } 
   public void visitTypeParameter(JCTypeParameter that) { try { print("JCTypeParameter:"); } catch (Exception e) {} super.visitTypeParameter(that); } 
   public void visitWildcard(JCWildcard that) { try { print("JCWildcard:"); } catch (Exception e) {} super.visitWildcard(that); } 
   public void visitTypeBoundKind(TypeBoundKind that) { try { print("TypeBoundKind:"); } catch (Exception e) {} super.visitTypeBoundKind(that); } 
   public void visitAnnotation(JCAnnotation that) { try { print("JCAnnotation:"); } catch (Exception e) {} super.visitAnnotation(that); } 
   public void visitModifiers(JCModifiers that) { try { print("JCModifiers:"); } catch (Exception e) {} super.visitModifiers(that); } 
   public void visitErroneous(JCErroneous that) { try { print("JCErroneous:"); } catch (Exception e) {} super.visitErroneous(that); } 
   public void visitLetExpr(LetExpr that) { try { print("LetExpr:"); } catch (Exception e) {} super.visitLetExpr(that); } 
   public void visitTree(JCTree that) { try { print("JCTree:"); } catch (Exception e) {} super.visitTree(that); } 
}
