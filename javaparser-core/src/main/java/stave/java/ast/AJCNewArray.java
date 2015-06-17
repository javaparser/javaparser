package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCNewArray extends JCNewArray implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCNewArray (JCExpression elemtype, List<JCExpression> dims, List<JCExpression> elems) {
      super( elemtype, dims, elems);
   }
   
   public AJCNewArray( JCNewArray ltree) {
      super( ltree.elemtype, ltree.dims, ltree.elems);
   }

   public AJCNewArray( JCNewArray ltree, String lcomment) {
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

