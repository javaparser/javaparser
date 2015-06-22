package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCBlock extends JCBlock implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCBlock (long flags, List<JCStatement> stats) {
      super( flags, stats);
   }
   
   public AJCBlock( JCBlock ltree) {
      super( ltree.flags, ltree.stats);
   }

   public AJCBlock( JCBlock ltree, String lcomment) {
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

