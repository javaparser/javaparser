package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCExpressionStatement extends JCExpressionStatement implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCExpressionStatement (JCExpression expr) {
      super( expr);
   }
   
   public AJCExpressionStatement( JCExpressionStatement ltree) {
      super( ltree.expr);
   }

   public AJCExpressionStatement( JCExpressionStatement ltree, String lcomment) {
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

