package stave.java.ast;

import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
//import com.sun.tools.javac.code.Scope.ImportScope;

public class AJCClassDecl extends JCClassDecl implements JavaParserComments {

   public String comment;

   public boolean hasComment() { return comment != null; }

   public AJCClassDecl(JCModifiers mods,
                 Name name,
                 List<JCTypeParameter> typarams,
                 JCExpression extending,
                 List<JCExpression> implementing,
                 List<JCTree> defs,
                 ClassSymbol sym) {
      super(mods, name, typarams, extending, implementing, defs, sym);
   }
   
   public AJCClassDecl( JCClassDecl ltree) {
      super(ltree.mods, ltree.name, ltree.typarams, ltree.extending, ltree.implementing, ltree.defs, ltree.sym);
   }

   public AJCClassDecl( JCClassDecl ltree, String lcomment) {
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

