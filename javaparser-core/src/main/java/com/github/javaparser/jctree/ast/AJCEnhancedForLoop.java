package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
//import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCEnhancedForLoop extends JCEnhancedForLoop implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCEnhancedForLoop (JCVariableDecl var, JCExpression expr, JCStatement body) {
      super( var, expr, body);
   }
   
   public AJCEnhancedForLoop( JCEnhancedForLoop ltree) {
      super( ltree.var, ltree.expr, ltree.body);
   }

   public AJCEnhancedForLoop( JCEnhancedForLoop ltree, String lcomment) {
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

