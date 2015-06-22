package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCImport extends JCImport implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCImport (JCTree qualid, boolean importStatic) {
      super( qualid, importStatic);
   }
   
   public AJCImport( JCImport ltree) {
      super( ltree.qualid, ltree.isStatic());
   }

   public AJCImport( JCImport ltree, String lcomment) {
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

