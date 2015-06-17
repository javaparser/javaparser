package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCModifiers extends JCModifiers implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCModifiers (long flags, List<JCAnnotation> annotations) {
      super( flags, annotations);
   }
   
   public AJCModifiers( JCModifiers ltree) {
      super( ltree.flags, ltree.annotations);
   }

   public AJCModifiers( JCModifiers ltree, String lcomment) {
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

