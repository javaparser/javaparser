package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCTry extends JCTry implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCTry( List<JCTree> resources,
           JCBlock body,
           List<JCCatch> catchers,
           JCBlock finalizer) {
      super( resources, body, catchers, finalizer);
   }
   
   public AJCTry( JCTry ltree) {
      super( ltree.resources, ltree.body, ltree.catchers, ltree.finalizer);
   }

   public AJCTry( JCTry ltree, String lcomment) {
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

