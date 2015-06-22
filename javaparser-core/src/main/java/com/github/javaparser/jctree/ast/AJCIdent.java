package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCIdent extends JCIdent implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCIdent (Name name, Symbol sym) {
      super( name, sym);
   }
   
   public AJCIdent( JCIdent ltree) {
      super( ltree.name, ltree.sym);
   }

   public AJCIdent( JCIdent ltree, String lcomment) {
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

