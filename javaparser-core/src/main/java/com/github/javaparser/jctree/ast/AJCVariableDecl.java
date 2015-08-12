package com.github.javaparser.jctree.ast;

import com.sun.tools.javac.tree.JCTree.*;
//import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.code.Symbol.*;
//import com.sun.tools.javac.code.Scope.ImportScope;
//import com.sun.tools.javac.code.BoundKind;

public class AJCVariableDecl extends JCVariableDecl implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCVariableDecl(JCModifiers mods,
                   Name name,
                   JCExpression vartype,
                   JCExpression init,
                   VarSymbol sym) {
      super(mods, name, vartype, init, sym);
   }
   
   public AJCVariableDecl( JCVariableDecl ltree) {
      super( ltree.mods, ltree.name, ltree.vartype, ltree.init, ltree.sym);
   }

   public AJCVariableDecl( JCVariableDecl ltree, String lcomment) {
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

