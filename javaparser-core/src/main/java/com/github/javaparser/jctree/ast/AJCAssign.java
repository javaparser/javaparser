package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCAssign extends JCAssign implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCAssign (JCExpression lhs, JCExpression rhs) {
      super( lhs, rhs);
   }
   
   public AJCAssign( JCAssign ltree) {
      super( ltree.lhs, ltree.rhs);
   }

   public AJCAssign( JCAssign ltree, String lcomment) {
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

