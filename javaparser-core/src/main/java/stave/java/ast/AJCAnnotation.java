package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCAnnotation extends JCAnnotation implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCAnnotation (JCTree annotationType, List<JCExpression> args) {
      super( annotationType, args);
   }
   
   public AJCAnnotation( JCAnnotation ltree) {
      super( ltree.annotationType, ltree.args);
   }

   public AJCAnnotation( JCAnnotation ltree, String lcomment) {
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

