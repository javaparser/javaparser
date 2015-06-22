package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCErroneous extends JCErroneous implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCErroneous (List<? extends JCTree> errs) {
      super( errs);
   }
   
   public AJCErroneous( JCErroneous ltree) {
      super( ltree.errs);
   }

   public AJCErroneous( JCErroneous ltree, String lcomment) {
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

