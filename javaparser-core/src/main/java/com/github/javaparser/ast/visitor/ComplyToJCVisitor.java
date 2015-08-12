/**
 * This visitor inserts transformations to the AST that
 * would also be introduced in by the official Java Compiler
 * Examples:
 * - Type var1, var2, var3; becomes Type var1; Type var2; Type var3;
 * - Addition of default contructor ClassName();
 */ 

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.*;

import java.util.List;
import java.util.Vector;

public class ComplyToJCVisitor extends ModifierVisitorAdapter<Object> {

   /* This flag stores if the visited class has a default constructor (i.e., with no arguments).
   * It must store and restores the previous values for each class declaration,
   * to avoid incorrect flagging in the presence of nested classes.
   */
   private boolean founddefault = false;

   protected static class ListFieldDeclaration extends BodyDeclaration {

      private List<FieldDeclaration> listfielddecl;

      // Constructor must get the complete list of expanded variables.
      public ListFieldDeclaration(List<FieldDeclaration> lvarslist) {
	 listfielddecl = lvarslist;
      }

      protected static FieldDeclaration makeClone(FieldDeclaration n) {
	 FieldDeclaration myclone = new FieldDeclaration( n.getBeginLine(),
                                                          n.getBeginColumn(),
                                                          n.getEndLine(),
                                                          n.getEndColumn(),
                                                          n.getModifiers(),
                                                          n.getAnnotations(),
                                                          n.getType(),
                                                          n.getVariables()
                                                        );

         // Clone class members inherited from Node
	 myclone.setParentNode(n.getParentNode());
	 myclone.setData( n.getData() );
	 myclone.setComment( n.getComment());
	 // Orphan comments should be added one by one
	 for (final Comment c: n.getOrphanComments() ) myclone.addOrphanComment(c);

	 return myclone;
      }

      public List<FieldDeclaration> getVarDecls() {
	 return listfielddecl;
      }

      @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) { return null; }
      @Override public <A> void accept(final VoidVisitor<A> v, final A arg) { ; }
   }

   // Inner class used to expand Variable declaration
   protected static class ListExpressionStmt extends Statement {

      private List<ExpressionStmt> listexprstmt;

      // Constructor must get the complete list of expanded variables.
      public ListExpressionStmt(List<ExpressionStmt> lvarslist) {
	 listexprstmt = lvarslist;
      }

      protected static ExpressionStmt makeClone(ExpressionStmt n) {
	 ExpressionStmt myclone = new ExpressionStmt( n.getBeginLine(),
                                                      n.getBeginColumn(),
                                                      n.getEndLine(),
                                                      n.getEndColumn(),
                                                      n.getExpression() );
         // Clone class members inherited from Node
	 myclone.setParentNode(n.getParentNode());
	 myclone.setData( n.getData() );
	 myclone.setComment( n.getComment());
	 // Orphan comments should be added one by one
	 for (final Comment c: n.getOrphanComments() ) myclone.addOrphanComment(c);

	 return myclone;
      }

      public List<ExpressionStmt> getVarStmts() {
	 return listexprstmt;
      }

      @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) { return null; }
      @Override public <A> void accept(final VoidVisitor<A> v, final A arg) { ; }
   }

   public Node visit(final ListExpressionStmt n, Object arg) {
      return n;
   }

   // Inner class used to expand Variable declaration
   protected static class ListVariableDeclarationExpr extends Expression {

      private List<VariableDeclarationExpr> listvardeclexpr;

      // Constructor must get the complete list of expanded variables.
      public ListVariableDeclarationExpr(List<VariableDeclarationExpr> lvarslist) {
	 listvardeclexpr = lvarslist;
      }

      protected static VariableDeclarationExpr makeClone(VariableDeclarationExpr n) {
	 VariableDeclarationExpr myclone = new VariableDeclarationExpr( n.getBeginLine(),
                                                                        n.getBeginColumn(),
                                                                        n.getEndLine(),
                                                                        n.getEndColumn(),
                                                                        n.getModifiers(),
                                                                        n.getAnnotations(),
                                                                        n.getType(),
                                                                        n.getVars() );
         // Clone class members inherited from Node
	 myclone.setParentNode(n.getParentNode());
	 myclone.setData( n.getData() );
	 myclone.setComment( n.getComment());
	 // Orphan comments should be added one by one
	 for (final Comment c: n.getOrphanComments() ) myclone.addOrphanComment(c);

	 return myclone;
      }

      public List<VariableDeclarationExpr> getVarExprs() {
	 return listvardeclexpr;
      }

      @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) { return null; }
      @Override public <A> void accept(final VoidVisitor<A> v, final A arg) { ; }
   }

   public Node visit(final ListVariableDeclarationExpr n, Object arg) {
      return n;
   }

   @Override public Node visit(final VariableDeclarationExpr n, Object arg) {

      Vector<VariableDeclarationExpr> lexprlist = new Vector<VariableDeclarationExpr>();

      for ( final VariableDeclarator v : n.getVars() ) {
         // Clone old object
         VariableDeclarationExpr lnewvar = ListVariableDeclarationExpr.makeClone(n);

         // Get Type-Name (VariableDeclarator)
         VariableDeclarator ltypename = (VariableDeclarator) v.accept(this, arg);
	 //lnewvar.setAsParentNodeOf( ltypename);

         // Creates VariableDeclarationExpr (lnewvar) with a single declaration
         Vector<VariableDeclarator> myunitvec = new Vector<VariableDeclarator>();
         myunitvec.add(ltypename);

         lnewvar.setVars(myunitvec);

         lexprlist.add( lnewvar );
      }

      // Finally create list with variable expressions and return.
      return new ListVariableDeclarationExpr( lexprlist );
   }

   @Override public Node visit(final BlockStmt n, final Object arg) {

      if (n.getStmts()!= null) {
         Vector<Statement> lnewlist = new Vector<Statement>();

	 for (final Statement s : n.getStmts() ) {
            Statement mystmt = (Statement) s.accept(this, arg);

            // Append the expanded list to list of Statements
            if (mystmt instanceof ListExpressionStmt) lnewlist.addAll( ((ListExpressionStmt)mystmt).getVarStmts() );
            else lnewlist.add( mystmt);
	 }
         n.setStmts(lnewlist);
      }
      return n;
   }

   @Override public Node visit(final ExpressionStmt n, Object arg) {
      // VariableDeclarationExpr contains a list of variable declaration
      // Unfolding it to several elements
      Node myresult = n.getExpression().accept(this,arg);

      // Checking if type is the expected one. Should be careful here.
      if (myresult instanceof ListVariableDeclarationExpr) {
	 Vector<ExpressionStmt> mydecllist = new Vector<ExpressionStmt>();

	 for (final VariableDeclarationExpr newexpr : ((ListVariableDeclarationExpr)myresult).getVarExprs() ) {

	    // Build an ExpressionStmt with same metadata as n
	    ExpressionStmt mynewstmt = ListExpressionStmt.makeClone(n);
	    // Set the unfolded variable declaration expression
	    mynewstmt.setExpression(newexpr);

	    mydecllist.add( mynewstmt );
	 }

	 return new ListExpressionStmt( mydecllist );
      } else {
         n.setExpression( (Expression) myresult);
         return n;
      }
   }

   @Override public Node visit(final FieldDeclaration n, Object arg) {
      // Field declaration contains a list of member declarations
      // Unfolding it to several elements

      Vector<FieldDeclaration> mydecllist = new Vector<FieldDeclaration>();

      for (final VariableDeclarator mynameinit : n.getVariables() ) {

	 // Build an FieldDeclaration with same metadata as n
	 FieldDeclaration myfield = ListFieldDeclaration.makeClone(n);

         // Creating the list (vector) that will contain single name/init declaration
         Vector<VariableDeclarator> myunitarylist = new Vector<VariableDeclarator>();
         myunitarylist.add( mynameinit);

         myfield.setVariables( myunitarylist);

	 mydecllist.add( myfield );
      }

      return new ListFieldDeclaration( mydecllist );
   }

   @Override public Node visit(final ClassOrInterfaceDeclaration n, final Object arg) {

      if ( ! (n.isInterface()) ) {

	 // Preserve the value of flag indicating that enclosing class
	 // has found the default constructor.
	 boolean storedprev = founddefault; 
         founddefault = false;

         // Generates a new list, which might even be empty.
	 Vector<BodyDeclaration> lnewlist = new Vector<BodyDeclaration>();

	 /* Code for unfolding field declaration */
	 if (n.getMembers()!= null) {
	    for (final BodyDeclaration b : n.getMembers() ) {
	       BodyDeclaration mydecl = (BodyDeclaration) b.accept(this, arg);

	       // Append the expanded list to list of bodydeclaration
	       if (mydecl instanceof ListFieldDeclaration) lnewlist.addAll( ((ListFieldDeclaration)mydecl).getVarDecls() );
	       else lnewlist.add( mydecl);
	    }
	 }

	 /* 
          Code for detecting declaration of default contructor.
	  Clone metadata from class declaration.
	  */
	 if (!(founddefault) ) {
	       lnewlist.add( new ConstructorDeclaration(n.getModifiers(),
		     new Vector<AnnotationExpr>(),
		     new Vector<TypeParameter>(),
		     n.getName(),
		     new Vector<Parameter>(),
		     new Vector<NameExpr>(),
		     new BlockStmt( new Vector<Statement>() ) ) );
         }

	 // Restore the value for the flag relative to enclosing class
	 founddefault = storedprev;

	 // Set the generated list
	 n.setMembers(lnewlist);
      }

      return n;
   }

   // Before returning, set the flag if has found a default constructors
   @Override public Node visit(final ConstructorDeclaration n, final Object arg) {
      ConstructorDeclaration myret = (ConstructorDeclaration) super.visit(n,arg);

      List<Parameter> parameters = n.getParameters();
      // I'd write short-circuit expression with ||,
      // but someone whom uses Eclipse would complain.
      if (parameters == null) {
         founddefault = true;
      } else if ( parameters.size() == 0) {
         founddefault = true;
      }

      return myret;
   }
}
