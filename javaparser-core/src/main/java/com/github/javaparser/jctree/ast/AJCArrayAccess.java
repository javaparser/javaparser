package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCArrayAccess extends JCArrayAccess implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCArrayAccess (JCExpression indexed, JCExpression index) {
      super( indexed, index);
   }
   
   public AJCArrayAccess( JCArrayAccess ltree) {
      super( ltree.indexed, ltree.index);
   }

   public AJCArrayAccess( JCArrayAccess ltree, String lcomment) {
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

