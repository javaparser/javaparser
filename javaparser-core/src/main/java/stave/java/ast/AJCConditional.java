package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCConditional extends JCConditional implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCConditional (JCExpression cond, JCExpression truepart, JCExpression falsepart) {
      super( cond, truepart, falsepart);
   }
   
   public AJCConditional( JCConditional ltree) {
      super( ltree.cond, ltree.truepart, ltree.falsepart);
   }

   public AJCConditional( JCConditional ltree, String lcomment) {
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

