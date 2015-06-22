package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCTypeApply extends JCTypeApply implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCTypeApply (JCExpression clazz, List<JCExpression> arguments) {
      super( clazz, arguments);
   }
   
   public AJCTypeApply( JCTypeApply ltree) {
      super( ltree.clazz, ltree.arguments);
   }

   public AJCTypeApply( JCTypeApply ltree, String lcomment) {
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

