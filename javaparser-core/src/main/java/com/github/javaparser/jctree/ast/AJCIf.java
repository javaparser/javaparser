package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCIf extends JCIf implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCIf (JCExpression cond, JCStatement thenpart, JCStatement elsepart) {
      super( cond, thenpart, elsepart);
   }
   
   public AJCIf( JCIf ltree) {
      super( ltree.cond, ltree.thenpart, ltree.elsepart);
   }

   public AJCIf( JCIf ltree, String lcomment) {
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

