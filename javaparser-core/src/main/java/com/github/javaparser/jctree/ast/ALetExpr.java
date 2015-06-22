package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class ALetExpr extends LetExpr implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public ALetExpr (List<JCVariableDecl> defs, JCTree expr) {
      super( defs, expr);
   }
   
   public ALetExpr( LetExpr ltree) {
      super( ltree.defs, ltree.expr);
   }

   public ALetExpr( LetExpr ltree, String lcomment) {
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

