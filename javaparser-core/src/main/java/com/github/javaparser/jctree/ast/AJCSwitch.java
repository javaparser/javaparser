package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
//import com.sun.tools.javac.util.Name;
//import com.sun.tools.javac.code.Symbol;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCSwitch extends JCSwitch implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCSwitch (JCExpression selector, List<JCCase> cases) {
      super( selector, cases);
   }
   
   public AJCSwitch( JCSwitch ltree) {
      super( ltree.selector, ltree.cases);
   }

   public AJCSwitch( JCSwitch ltree, String lcomment) {
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

