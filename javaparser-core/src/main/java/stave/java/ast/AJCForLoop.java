package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCForLoop extends JCForLoop implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCForLoop (List<JCStatement> init,
              JCExpression cond,
              List<JCExpressionStatement> update,
              JCStatement body) {
      super( init, cond, update, body);
   }
   
   public AJCForLoop( JCForLoop ltree) {
      super( ltree.init, ltree.cond, ltree.step, ltree.body);
   }

   public AJCForLoop( JCForLoop ltree, String lcomment) {
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

