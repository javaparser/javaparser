package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCCase extends JCCase implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCCase (JCExpression pat, List<JCStatement> stats) {
      super( pat, stats);
   }
   
   public AJCCase( JCCase ltree) {
      super( ltree.pat, ltree.stats);
   }

   public AJCCase( JCCase ltree, String lcomment) {
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

