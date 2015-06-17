package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCUnary extends JCUnary implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCUnary (int opcode, JCExpression arg) {
      super( opcode, arg);
   }
   
   public AJCUnary( JCUnary ltree) {
      super( ltree.getTag(), ltree.arg);
   }

   public AJCUnary( JCUnary ltree, String lcomment) {
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

