package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCMethodInvocation extends JCMethodInvocation implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCMethodInvocation(List<JCExpression> typeargs, JCExpression meth, List<JCExpression> args) {
      super(typeargs, meth, args);
   }
   
   public AJCMethodInvocation( JCMethodInvocation ltree) {
      super(ltree.typeargs, ltree.meth, ltree.args);
   }

   public AJCMethodInvocation( JCMethodInvocation ltree, String lcomment) {
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

