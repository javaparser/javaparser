package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCAssignOp extends JCAssignOp implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCAssignOp (int opcode, JCTree lhs, JCTree rhs, Symbol operator) {
      super( opcode, lhs, rhs, operator);
   }
   
   public AJCAssignOp( JCAssignOp ltree) {
      super( ltree.getTag(), ltree.lhs, ltree.rhs, ltree.operator);
   }

   public AJCAssignOp( JCAssignOp ltree, String lcomment) {
      this(ltree);
      setComment(lcomment);
   }

   public String getComment() {
      return comment;
   }

   public void setComment(String lcomment) {
      comment = lcomment;
   }
}

