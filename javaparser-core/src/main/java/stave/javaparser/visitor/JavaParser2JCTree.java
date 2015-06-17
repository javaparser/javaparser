/*
 * Copyright (C) 2007-2010 Julio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 * Editied by: Pedro de Carvalho Gomes
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOJCTree Object PARTICULAJCTree PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package stave.javaparser.visitor;

import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EmptyMemberDeclaration;
import com.github.javaparser.ast.body.EmptyTypeDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.ModifierSet;
import com.github.javaparser.ast.body.MultiTypeParameter;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.ForeachStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntryStmt;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.TypeDeclarationStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitor;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.*;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

import javax.lang.model.type.TypeKind;

import stave.java.ast.*;

import static com.sun.tools.javac.code.BoundKind.*;
/**
 * @author Pedro de Carvalho Gomes
 */
public class JavaParser2JCTree implements GenericVisitor<JCTree, Object> {

   private TreeMaker make;
   private Name.Table names;

   public JavaParser2JCTree(Context context) {
      make = TreeMaker.instance(context);
      names = Names.instance(context).table;
   }

   @Override
      public JCTree visit(final AnnotationDeclaration n, final Object arg) {
         /* TODO - Annotations are not currently supported
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
	 if (n.getMembers() != null) {
	    for (final BodyDeclaration member : n.getMembers()) {
		  JCTree result = member.accept(this, arg);
	    }
	 }

	 return new AJCAnnotationDeclaration( make.AnnotationDeclaration( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final AnnotationMemberDeclaration n, final Object arg) {
         /* TODO - Annotations are not currently supported
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
	 JCTree result = n.getType().accept(this, arg);
	 if (n.getDefaultValue() != null) {
	       JCTree result = n.getDefaultValue().accept(this, arg);
	 }
	 return new AJCAnnotationMemberDeclaration( make.AnnotationMemberDeclaration( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final ArrayAccessExpr n, final Object arg) {
         //ARG0: JCExpression indexed
	 JCExpression arg0 = (JCExpression) n.getName().accept(this, arg);

         //ARG1: JCExpression index
	 JCExpression arg1 = (JCExpression) n.getIndex().accept(this, arg);

	 return new AJCArrayAccess( make.Indexed( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ArrayCreationExpr n, final Object arg) {
	 //ARG0: JCExpression elemtype
	 JCExpression arg0 = (JCExpression) n.getType().accept(this, arg);

         // TODO - An array may be initialized with dimentions or assiginig elements.
         // Java Parser treats these options as mutual exclusive but JCTree don't. 
         // Confirm which is correct.

	 //ARG1: List<JCExpression> dims
	 List<JCExpression> arg1 = List.<JCExpression>nil();
	 if (n.getDimensions() != null) {
	    for (final Expression dim : n.getDimensions()) {
	       arg1 = arg1.append( (JCExpression) dim.accept(this, arg));
	    }
	 } 

	 //ARG2: List<JCExpression> elems
	 List<JCExpression> arg2 = List.<JCExpression>nil();
	 if ( n.getInitializer().getValues() != null) {
	    for (final Expression expr : n.getInitializer().getValues()) {
	       arg2 = arg2.append( (JCExpression) expr.accept(this, arg));
	    }
	 }

	 return new AJCNewArray( make.NewArray( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ArrayInitializerExpr n, final Object arg) {
	 //ARG0: JCExpression elemtype
         // This is for the type of elements in, e.g., int[][] a = {{1,2},{3,4}};
         // Field not necessary
	 JCExpression arg0 = null;

	 //ARG1: List<JCExpression> dims
         // Field not necessary.
	 List<JCExpression> arg1 = List.<JCExpression>nil();

	 //ARG2: List<JCExpression> elems
	 List<JCExpression> arg2 = List.<JCExpression>nil();
	 if (n.getValues() != null) {
	    for (final Expression expr : n.getValues()) {
	       arg2 = arg2.append( (JCExpression) expr.accept(this, arg));
	    }
	 }

	 return new AJCNewArray( make.NewArray( arg0, arg1, arg2), null );
         
      }

   @Override
      public JCTree visit(final AssertStmt n, final Object arg) {
         //ARG0: JCExpression cond
	 JCExpression arg0 = (JCExpression) n.getCheck().accept(this, arg);

         //ARG1: JCExpression detail
         JCExpression arg1 = null;
	 if (n.getMessage() != null) {
	      arg1 = (JCExpression) n.getMessage().accept(this, arg);
	 }

	 return new AJCAssert( make.Assert( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final AssignExpr n, final Object arg) {
         // ARG0: int opcode 
         int arg0;

         // ARG1: JCExpression lhs
         JCExpression arg1 = (JCExpression) n.getTarget().accept(this, arg);

         // ARG2: JCExpression rhs
         JCExpression arg2 = (JCExpression) n.getValue().accept(this, arg);

         // JCTree has two distinct nodes for Assigment
         // The following case if for pure assignment "="
         if (n.getOperator() == AssignExpr.Operator.assign) {
	    return new AJCAssign( make.Assign( arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         }

         // Cases for operation followed by assignment
         switch(n.getOperator()) {
            case plus:           arg0 = JCTree.PLUS_ASG; break;
            case minus:          arg0 = JCTree.MINUS_ASG; break;
            case star:           arg0 = JCTree.MUL_ASG; break;
            case slash:          arg0 = JCTree.DIV_ASG; break;
            case and:            arg0 = JCTree.BITAND_ASG; break;
            case or:             arg0 = JCTree.BITOR_ASG; break;
            case xor:            arg0 = JCTree.BITXOR_ASG; break;
            case rem:            arg0 = JCTree.MOD_ASG; break;
            case lShift:         arg0 = JCTree.SL_ASG; break;
            case rSignedShift:   arg0 = JCTree.SR_ASG; break;
            case rUnsignedShift: arg0 = JCTree.USR_ASG; break;
            default:             arg0 = JCTree.ERRONEOUS;
         }

	 return new AJCAssignOp( make.Assignop( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final BinaryExpr n, final Object arg) {
         //ARG0: int opcode
         int arg0;

         switch(n.getOperator()) {
            case or:             arg0 = JCTree.OR; break;
            case and:            arg0 = JCTree.AND; break;
            case binOr:          arg0 = JCTree.BITOR; break;
            case binAnd:         arg0 = JCTree.BITAND; break;
            case xor:            arg0 = JCTree.BITXOR; break;
            case equals:         arg0 = JCTree.EQ; break;
            case notEquals:      arg0 = JCTree.NE; break;
            case less:           arg0 = JCTree.LT; break;
            case greater:        arg0 = JCTree.GT; break;
            case lessEquals:     arg0 = JCTree.LE; break;
            case greaterEquals:  arg0 = JCTree.GE; break;
            case lShift:         arg0 = JCTree.SL; break;
            case rSignedShift:   arg0 = JCTree.SR; break;
            case rUnsignedShift: arg0 = JCTree.USR; break;
            case plus:           arg0 = JCTree.PLUS; break;
            case minus:          arg0 = JCTree.MINUS; break;
            case times:          arg0 = JCTree.MUL; break;
            case divide:         arg0 = JCTree.DIV; break;
            case remainder:      arg0 = JCTree.MOD; break;
            default:             arg0 = JCTree.ERRONEOUS;
         }

         //ARG1: JCExpression lhs
	 JCExpression arg1 = (JCExpression) n.getLeft().accept(this, arg);

         //ARG2: JCExpression rhs
	 JCExpression arg2 = (JCExpression) n.getRight().accept(this, arg);

	 return new AJCBinary( make.Binary( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final BlockStmt n, final Object arg) {
         // ARG0: long flags
         // It is logically endend with Flags.STATIC is static init
         long arg0 = 0;
         
         // ARG1: List<JCStatement> stats
         List<JCStatement> arg1 = List.<JCStatement>nil();
	 if (n.getStmts() != null) {
	    for (final Statement s : n.getStmts()) {
		  arg1 = arg1.append( (JCStatement) s.accept(this, arg));
	    }
	 }

	 return new AJCBlock( make.Block( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final BooleanLiteralExpr n, final Object arg) {
         //ARG0: Object value
         // The type if literals are tested with instance of
         // inside Literal
         Boolean arg0 = new Boolean( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final BreakStmt n, final Object arg) {
         //ARG0: Name label
         Name arg0 = names.fromString( n.getId());

	 return new AJCBreak( make.Break( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final CastExpr n, final Object arg) {
         ///ARG0: JCTree clazz
	 JCTree arg0 = n.getType().accept(this, arg);

         ///ARG1: JCExpression expr
	 JCExpression arg1 = (JCExpression) n.getExpr().accept(this, arg);

	 return new AJCTypeCast( make.TypeCast( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final CatchClause n, final Object arg) {
         //JCVariableDecl param
         JCVariableDecl arg0 = (JCVariableDecl) n.getExcept().accept(this, arg);

         //ARG1: JCBlock body
	 JCBlock arg1 = (JCBlock) n.getCatchBlock().accept(this, arg);

	 return new AJCCatch( make.Catch( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final CharLiteralExpr n, final Object arg) {
         //ARG0: Object value
         Character arg0 = new Character( n.getValue().charAt(0));

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ClassExpr n, final Object arg) {
         //ARG0: JCExpression selected
         // I am assuming type is ClassOrInterfaceType
	 JCExpression arg0 = (JCExpression) n.getType().accept(this, arg);

         //ARG1: Name selector
         Name arg1 = names.fromString("class");

	 return new AJCFieldAccess( make.Select( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   /**
   * @param ljpmodif modifiers in JavaParser style
   * @param lsouce set of flags already set
   * @return Flags previously set, plus the ones provided as the first argument
   */
   private long setJCTreeModifiers( int ljpmodif, long lsource) {
      if (ModifierSet.isPublic(ljpmodif))       lsource |= Flags.PUBLIC;
      if (ModifierSet.isPrivate(ljpmodif))      lsource |= Flags.PRIVATE;
      if (ModifierSet.isProtected(ljpmodif))    lsource |= Flags.PROTECTED;
      if (ModifierSet.isStatic(ljpmodif))       lsource |= Flags.STATIC;
      if (ModifierSet.isFinal(ljpmodif))        lsource |= Flags.FINAL;
      if (ModifierSet.isSynchronized(ljpmodif)) lsource |= Flags.SYNCHRONIZED;
      if (ModifierSet.isVolatile(ljpmodif))     lsource |= Flags.VOLATILE;
      if (ModifierSet.isTransient(ljpmodif))    lsource |= Flags.TRANSIENT;
      if (ModifierSet.isStrictfp(ljpmodif))     lsource |= Flags.STRICTFP;
      if (ModifierSet.isNative(ljpmodif))       lsource |= Flags.NATIVE;
      if (ModifierSet.isAbstract(ljpmodif))     lsource |= Flags.ABSTRACT;
  
      return (lsource);
   }

   @Override
      public JCTree visit(final ClassOrInterfaceDeclaration n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;

         // Must convert internal modifiers
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         // Interface is a flag for JCTree, but not for Java Parser. Setting separetely 
         if (n.isInterface()) jcmodifier |= Flags.INTERFACE; 

         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         //ARG1: Name name
         Name arg1 = names.fromString(n.getName());

         /* TODO - Check what to do with annotations
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */
 
         //ARG2: List<JCTypeParameter> typarams
         List<JCTypeParameter> arg2 = List.<JCTypeParameter>nil();
	 if (n.getTypeParameters() != null) {
	    for (final TypeParameter t : n.getTypeParameters()) {
		  arg2 = arg2.append( (JCTypeParameter) t.accept(this, arg));
	    }
	 }

         //ARG3: JCExpression extending
         JCExpression arg3 = null;

         //ARG4: List<JCExpression> implementing
         List<JCExpression> arg4 = List.<JCExpression>nil(); 

         // JCTree passes "extends" from interfaces in the same 
         // data structure as "implements" for Classes
         // JavaParser divide the sets by the literal used,
         // regardless if comming from a class or interface
	 if ((n.isInterface())) {
	    if (n.getExtends() != null) {
	       for (final ClassOrInterfaceType c : n.getExtends()) {
		  arg4 = arg4.append( (JCExpression) c.accept(this, arg));
	       }
	    }
            /** There should be no elements here, since it's an interface.
	    if (n.getImplements() != null) {
	       for (final ClassOrInterfaceType c : n.getImplements()) {
		  arg4 = arg4.append( c.accept(this, arg));
	       }
	    }
            */
	 } else {
	    if (n.getExtends() != null) {
               // There should be a single element in such list
	       for (final ClassOrInterfaceType c : n.getExtends()) {
		  arg3 = (JCExpression) c.accept(this, arg);
	       }
	    }
	    if (n.getImplements() != null) {
	       for (final ClassOrInterfaceType c : n.getImplements()) {
		  arg4 = arg4.append( (JCExpression) c.accept(this, arg));
	       }
	    }
         }

         //ARG5: List<JCTree> defs
         List<JCTree> arg5 = List.<JCTree>nil();
	 if (n.getMembers() != null) {
	    for (final BodyDeclaration member : n.getMembers()) {
		  arg5 = arg5.append( member.accept(this, arg));
	    }
	 }

	 return new AJCClassDecl( make.ClassDef( arg0, arg1, arg2, arg3, arg4, arg5), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ClassOrInterfaceType n, final Object arg) {
         //ARG0: JCExpression selected
         JCExpression arg0;

         if (n.getTypeArgs() == null) {
	    //ARG1: Name name
	    Name arg1 = names.fromString(n.getName());

	    // There's not namespace to resolve. Returning the class name
	    if (n.getScope() == null) {
	       return new AJCIdent( make.Ident( arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
	    }

	    arg0 = (JCExpression) n.getScope().accept(this, arg);

	    // This a non-parametrized type 
	    if (n.getTypeArgs() == null ) return new AJCFieldAccess( make.Select( arg0,arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
	 }

	 // There's not namespace to resolve. Returning the class name
         Name myclassname = names.fromString(n.getName());
	 if (n.getScope() == null) {
	    arg0 = new AJCIdent( make.Ident( myclassname), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
	 } else {
            JCExpression myselector = (JCExpression) n.getScope().accept(this, arg);
            arg0 = new AJCFieldAccess( make.Select( myselector, myclassname), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         }

         //ARG1: <JCExpression> arguments
	 List<JCExpression> arg1 = List.<JCExpression>nil();

         if (n.getTypeArgs() != null) {
	    for (final com.github.javaparser.ast.type.Type t : n.getTypeArgs()) {
	       arg1 = arg1.append( (JCExpression) t.accept(this, arg));
	    }
	 }
         
         return new AJCTypeApply( make.TypeApply( arg0,arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final CompilationUnit n, final Object arg) {
	 // ARG0: List<JCAnnotation> packageAnnotations
	 List<JCAnnotation> arg0 = List.<JCAnnotation>nil();

	 // ARG1: JCExpression pid
         // Package declaration
	 JCExpression arg1 = null;

	 if (n.getPackage() != null) {
	    arg1 = (JCExpression) n.getPackage().accept(this, arg);

	    if (n.getPackage().getAnnotations() != null) {
	       for (final AnnotationExpr packageAnnotation : n.getPackage().getAnnotations() ) {
		  arg0 = arg0.append((JCAnnotation) packageAnnotation.accept(this, arg)) ;
	       }
	    }
	 }

	 // ARG2 = List<JCTree> defs
         // Imports and classes are passed in the same structure
	 List<JCTree> arg2 = List.<JCTree>nil();
	 if (n.getImports() != null) {
	    for (final ImportDeclaration i : n.getImports()) {
	       arg2 = arg2.append( i.accept(this, arg));
	    }
	 }
	 if (n.getTypes() != null) {
	    for (final TypeDeclaration typeDeclaration : n.getTypes()) {
	       arg2 = arg2.append( typeDeclaration.accept(this, arg));
	    }
	 }

	 return new AJCCompilationUnit( make.TopLevel(arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ConditionalExpr n, final Object arg) {
	 //ARG0: JCExpression cond,
	 JCExpression arg0 = (JCExpression) n.getCondition().accept(this, arg);

	 //ARG1: JCExpression thenpart
	 JCExpression arg1 = (JCExpression) n.getThenExpr().accept(this, arg);

	 //ARG2: JCExpression elsepart
	 JCExpression arg2 = (JCExpression) n.getElseExpr().accept(this, arg);

	 return new AJCConditional( make.Conditional( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ConstructorDeclaration n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;

         // Must convert internal modifiers
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         //ARG1: Name name
         // Names already has the name for this
         Name arg1 = names.names.init;

         //ARG2: JCExpression restype
         JCExpression arg2 = null;

         //ARG3: List<JCTypeParameter> typaramsList
         List<JCTypeParameter> arg3 = List.<JCTypeParameter>nil();
	 if (n.getTypeParameters() != null) {
	    for (final TypeParameter t : n.getTypeParameters()) {
	       arg3 = arg3.append( (JCTypeParameter) t.accept(this, arg));
	    }
	 }

         //ARG4: List<JCVariableDecl> params
         List<JCVariableDecl> arg4 = List.<JCVariableDecl>nil();
	 if (n.getParameters() != null) {
	    for (final Parameter p : n.getParameters()) {
	       arg4 = arg4.append( (JCVariableDecl) p.accept(this, arg));
	    }
	 }

         //ARG5: List<JCExpression> thrown
         List<JCExpression> arg5 = List.<JCExpression>nil();
	 if (n.getThrows() != null) {
	    for (final NameExpr name : n.getThrows()) {
	       arg5 = arg5.append( (JCExpression) name.accept(this, arg));
	    }
	 }

         //ARG6: JCBlock body
	 JCBlock arg6 = (JCBlock) n.getBlock().accept(this, arg);

         //ARG7: JCExpression defaultValue
         JCExpression arg7 = null;

         /* TODO - Javadoc and annotations not supported
	 if (n.getJavaDoc() != null) {
	    JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
	       JCTree result = a.accept(this, arg);
	    }
	 }
         */ 

	 return new AJCMethodDecl( make.MethodDef( arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ContinueStmt n, final Object arg) {
         //ARG0: Name label
         Name arg0 = names.fromString( n.getId());

	 return new AJCContinue( make.Continue( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final DoStmt n, final Object arg) {
         //ARG0: JCStatement body
	 JCStatement arg0 = (JCStatement) n.getBody().accept(this, arg);

         //ARG1: JCExpression cond
	 JCExpression arg1 = (JCExpression) n.getCondition().accept(this, arg);

	 return new AJCDoWhileLoop( make.DoLoop( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final DoubleLiteralExpr n, final Object arg) {
         //ARG0: Object value
         Double arg0 = new Double( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final EmptyMemberDeclaration n, final Object arg) {
         /* TODO - Check how to proceed here since an empty member should
         * be represented by an empty list
	 if (n.getJavaDoc() != null) {
	    JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 return new AJCEmptyMemberDeclaration( make.EmptyMemberDeclaration( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final EmptyStmt n, final Object arg) {
         // ARG0: long flags
         // Empty is just an empty block
         long arg0 = 0;
         
         // ARG1: List<JCStatement> stats
         List<JCStatement> arg1 = List.<JCStatement>nil();

	 return new AJCBlock( make.Block( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final EmptyTypeDeclaration n, final Object arg) {
         /* TODO - Check how to proceed here since an empty type should
         * be represented by an empty list
	 if (n.getJavaDoc() != null) {
	    {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	       if (result != null) {
		  return result;
	       }
	    }
	 }
	 return new AJCEmptyTypeDeclaration( make.EmptyTypeDeclaration( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final EnclosedExpr n, final Object arg) {
         //ARG0: JCExpression expr
	 JCExpression arg0 = (JCExpression) n.getInner().accept(this, arg);

	 return new AJCParens( make.Parens( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final EnumConstantDeclaration n, final Object arg) {
         //ARG0: JCExpression meth
         JCExpression arg0 = new AJCIdent( make.Ident( names.fromString( n.getName())), null);

         /*
	 if (n.getJavaDoc() != null) {
	    JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */ 

         //ARG1: List<JCExpression> args
         List<JCExpression> arg1 = List.<JCExpression>nil();
         // JCTree adds a string with name as first parameter
         arg1 = arg1.append( new AJCLiteral( make.Literal( n.getName()), null) );
	 if (n.getArgs() != null) {
	    for (final Expression e : n.getArgs()) {
		  arg1 = arg1.append( (JCExpression) e.accept(this, arg));
	    }
	 }

         /* TODO - Not treating method declarations yet
	 if (n.getClassBody() != null) {
	    for (final BodyDeclaration member : n.getClassBody()) {
		  JCTree result = member.accept(this, arg);
	    }
	 }
         */

	 return new AJCMethodInvocation( make.App( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final EnumDeclaration n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;

         // Must convert internal modifiers
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);

         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         //ARG1: Name name
         Name arg1 = names.fromString( n.getName());

         //ARG2: List<JCTypeParameter> typarams,
         List<JCTypeParameter> arg2 = List.<JCTypeParameter>nil();

         //ARG3: JCExpression extending,
         JCExpression arg3 = null;

         /*
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */

         //ARG4: List<JCExpression> implementing
         List<JCExpression> arg4 = List.<JCExpression>nil();
	 if (n.getImplements() != null) {
	    for (final ClassOrInterfaceType c : n.getImplements()) {
		  arg4 = arg4.append( (JCExpression) c.accept(this, arg));
	    }
	 }

         //ARG5: List<JCTree> defs
         // JCTree groups the const declaration and other declarations into the same list
         List<JCTree> arg5 = List.<JCTree>nil();
	 if (n.getEntries() != null) {
	    for (final EnumConstantDeclaration e : n.getEntries()) {
		  arg5 = arg5.append( e.accept(this, arg));
	    }
	 }
	 if (n.getMembers() != null) {
	    for (final BodyDeclaration member : n.getMembers()) {
		  arg5 = arg5.append( member.accept(this, arg));
	    }
	 }

	 return new AJCClassDecl( make.ClassDef( arg0, arg1, arg2, arg3, arg4, arg5), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ExplicitConstructorInvocationStmt n, final Object arg) {
         //ARG0: List<JCExpression> typeargs
         List<JCExpression> arg0 = List.<JCExpression>nil();
	 if (n.getTypeArgs() != null) {
	    for (final com.github.javaparser.ast.type.Type t : n.getTypeArgs()) {
		  arg0 = arg0.append( (JCExpression) t.accept(this, arg));
	    }
	 }

         //ARG1: JCExpression fn
         JCExpression arg1;
	 if (n.isThis()) {
            arg1 = new AJCIdent( make.Ident( names.fromString("this")), null);
	 } else {
	    if (n.getExpr() != null) {
		  arg1 = new AJCFieldAccess( make.Select( (JCExpression) n.getExpr().accept(this, arg), names.fromString("super")), null);
	    } else {
                  arg1 = new AJCIdent( make.Ident(names.fromString("super")), null);
            }
         }

         //ARG2: List<JCExpression> args
         List<JCExpression> arg2 = List.<JCExpression>nil();
	 if (n.getArgs() != null) {
	    for (final Expression e : n.getArgs()) {
		  arg2 = arg2.append( (JCExpression) e.accept(this, arg));
	    }
	 }

         // It is expected a Statement, so converting the invocation
         
	 return new AJCExpressionStatement( make.Exec( new AJCMethodInvocation(make.Apply( arg0, arg1, arg2), null) ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ExpressionStmt n, final Object arg) {
         //ARG0: JCExpression expr
         JCExpression arg0;

         JCTree mystmt = n.getExpression().accept(this, arg);
       
         // Adding commment if 
         // 1 - There's actualy a comment to add
         // 2 - The variable doesn't have a comment yet 
         // 3 - It is a variable declaration
         if ( (n.getComment()!=null) &&
              (!((AJCVariableDecl)mystmt).hasComment()) &&
              (mystmt instanceof AJCVariableDecl) ) {

            ((AJCVariableDecl)mystmt).setComment(n.getComment().getContent());
         }

         // Case where the expression is already a subclass of JCStatement, such as JCVariableDecl
         if (mystmt instanceof JCStatement) {
            return mystmt;
         }

         arg0 = (JCExpression) mystmt; 

	 return new AJCExpressionStatement( make.Exec( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final FieldAccessExpr n, final Object arg) {
         //ARG0: JCExpression selected
	 JCExpression arg0 = (JCExpression) n.getScope().accept(this, arg);

         //ARG1: Name selector
         Name arg1 = names.fromString( n.getField());

	 return new AJCFieldAccess( make.Select( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final FieldDeclaration n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;

         // Must convert internal modifiers
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         /* TODO - Ignoring Javadoc and annotations
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 } */

         //ARG1: Name name
         Name arg1 = null;

         //ARG2: JCExpression vartype
         JCExpression arg2 = (JCExpression) n.getType().accept(this, arg);

         //ARG3: JCExpression init
         JCExpression arg3 = null;

         // Does not support multiple declaration of fields from the same type.
         // Currently only the last one is preserved.
         // We assume that ComplyJCVisitor has unfolded  wrapped declarations before.
	 for (final VariableDeclarator var : n.getVariables()) {
	       arg1 = names.fromString(var.getId().getName());
               if (var.getInit() != null)
                  arg3 = (JCExpression) var.getInit().accept(this, arg);
               else
                  arg3 = null;
	 }


	 return new AJCVariableDecl( make.VarDef( arg0, arg1, arg2, arg3), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ForeachStmt n, final Object arg) {
         //ARG0: JCVariableDecl var
	 JCVariableDecl arg0 = (JCVariableDecl) n.getVariable().accept(this, arg);

         //ARG1: JCExpression expr
	 JCExpression arg1 = (JCExpression) n.getIterable().accept(this, arg);

         //ARG2: JCStatement body
	 JCStatement arg2 = (JCStatement) n.getBody().accept(this, arg);

	 return new AJCEnhancedForLoop( make.ForeachLoop( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ForStmt n, final Object arg) {
	 //ARG0: List<JCStatement> init
	 List<JCStatement> arg0 = List.<JCStatement>nil();
	 if (n.getInit() != null) {
	    for (final Expression e : n.getInit()) {
	       arg0 = arg0.append( (JCStatement) e.accept(this, arg));
	    }
	 }

	 //ARG1: JCExpression cond
	 JCExpression arg1 = null;
	 if (n.getCompare() != null) {
	    arg1 = (JCExpression) n.getCompare().accept(this, arg);
	 }

	 //ARG2: List<JCExpressionStatement> step
	 List<JCExpressionStatement> arg2 = List.<JCExpressionStatement>nil();
	 if (n.getUpdate() != null) {
	    for (final Expression e : n.getUpdate()) {
	       arg2 = arg2.append( (JCExpressionStatement) e.accept(this, arg));
	    }
	 }

	 //ARG3: JCStatement body
	 JCStatement arg3 = (JCStatement) n.getBody().accept(this, arg);

	 return new AJCForLoop( make.ForLoop( arg0, arg1, arg2, arg3), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final IfStmt n, final Object arg) {
	 //ARG0: JCExpression cond
	 JCExpression arg0 = (JCExpression) n.getCondition().accept(this, arg);

	 //ARG1: JCStatement thenpart
	 JCStatement arg1 = (JCStatement) n.getThenStmt().accept(this, arg);

	 //ARG2: JCStatement elsepart
         JCStatement arg2 = null;
	 if (n.getElseStmt() != null) {
	    arg2 = (JCStatement) n.getElseStmt().accept(this, arg);
	 }

	 return new AJCIf( make.If( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ImportDeclaration n, final Object arg) {
         //ARG0: JCTree qualid
         JCTree arg0;

         JCExpression packagename = (JCExpression) n.getName().accept(this, arg);
         // JavaParser remove asterisk from name. Adding it back;
         if ( n.isAsterisk()) {
            arg0 = new AJCFieldAccess( make.Select( packagename, names.fromString("*")), null);
         } else {
            arg0 = packagename;
         }

         //ARG1: boolean importStatic
         boolean arg1 = n.isStatic();

	 return new AJCImport( make.Import( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final InitializerDeclaration n, final Object arg) {
         //ARG0: long flags
         long arg0 = ModifierSet.STATIC;

         /* TODO - Ignoring javadoc 
	 if (n.getJavaDoc() != null) {
	       JCTree result = n.getJavaDoc().accept(this, arg);
	 }
         */

         //ARG1: List<JCStatement> stats
         List<JCStatement> arg1 = List.<JCStatement>nil();
         if (n.getBlock().getStmts() != null) {
            for (final Statement s : n.getBlock().getStmts()) {
                  arg1 = arg1.append( (JCStatement) s.accept(this, arg));
            }
         }
	 return new AJCBlock( make.Block( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final InstanceOfExpr n, final Object arg) {
         //ARG0: JCExpression expr
         JCExpression arg0 = (JCExpression) n.getExpr().accept(this, arg);

         //ARG1: JCTree clazz
	 JCTree arg1 = n.getType().accept(this, arg);

	 return new AJCInstanceOf( make.TypeTest( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final IntegerLiteralExpr n, final Object arg) {
         //ARG0: Object value
         Integer arg0 = new Integer( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final IntegerLiteralMinValueExpr n, final Object arg) {
         //ARG0: Object value
         Integer arg0 = new Integer( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final JavadocComment n, final Object arg) {
         /* TODO - Not processing Javadoc
	 return new AJCJavadocComment( make.JavadocComment( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final LabeledStmt n, final Object arg) {
         //ARG0: Name label
         Name arg0 = names.fromString( n.getLabel());

         //ARG1: JCStatement body
	 JCStatement arg1 = (JCStatement) n.getStmt().accept(this, arg);

	 return new AJCLabeledStatement( make.Labelled( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final LongLiteralExpr n, final Object arg) {
         //ARG0: Object value
         Long arg0 = new Long( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final LongLiteralMinValueExpr n, final Object arg) {
         //ARG0: Object value
         Long arg0 = new Long( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final MarkerAnnotationExpr n, final Object arg) {
         /* TODO - Currently not supporting annotations
	 JCTree result = n.getName().accept(this, arg);
	 return new AJCMarkerAnnotation( make.MarkerAnnotation( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final MemberValuePair n, final Object arg) {
         /* TODO - Used in the member/value annotations
         * However, annotations are not supported yet
	 {
	    JCTree result = n.getValue().accept(this, arg);
	    if (result != null) {
	       return result;
	    }
	 }
	 return new AJCMemberValuePair( make.MemberValuePair( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final MethodCallExpr n, final Object arg) {
         //ARG0: List<JCExpression> typeargs
         List<JCExpression> arg0 = List.<JCExpression>nil();
	 if (n.getTypeArgs() != null) {
	    for (final com.github.javaparser.ast.type.Type t : n.getTypeArgs()) {
	       arg0 = arg0.append( (JCExpression) t.accept(this, arg));
	    }
	 }

         //ARG1: JCExpression fn
         JCFieldAccess arg1;
         JCExpression selected = null;
	 if (n.getScope() != null) {
            selected = (JCExpression) n.getScope().accept(this, arg);
	 }
         arg1 = new AJCFieldAccess( make.Select(selected, names.fromString(n.getName())), null);

         //ARG2: List<JCExpression> args
         List<JCExpression> arg2 = List.<JCExpression>nil();
	 if (n.getArgs() != null) {
	    for (final Expression e : n.getArgs()) {
	       arg2 = arg2.append( (JCExpression) e.accept(this, arg));
	    }
	 }

	 return new AJCMethodInvocation( make.Apply( arg0, arg1, arg2), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final MethodDeclaration n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;

         // Must convert internal modifiers
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         //ARG1: Name name
         Name arg1 = names.fromString(n.getName());

         /* TODO - Not supporting javadoc nor annotations
	 if (n.getJavaDoc() != null) {
	    JCTree result = n.getJavaDoc().accept(this, arg);
	 }
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
	       JCTree result = a.accept(this, arg);
	    }
	 }
         */

         //ARG2: JCExpression restype
	 JCExpression arg2 = (JCExpression) n.getType().accept(this, arg);

         //ARG3: List<JCTypeParameter> typarams
         List<JCTypeParameter> arg3 = List.<JCTypeParameter>nil();
	 if (n.getTypeParameters() != null) {
	    for (final TypeParameter t : n.getTypeParameters()) {
	       arg3 = arg3.append( (JCTypeParameter) t.accept(this, arg));
	    }
	 }

         //ARG4: List<JCVariableDecl> params
         List<JCVariableDecl> arg4 = List.<JCVariableDecl>nil();
	 if (n.getParameters() != null) {
	    for (final Parameter p : n.getParameters()) {
	       arg4 = arg4.append( (JCVariableDecl) p.accept(this, arg));
	    }
	 }

         //ARG5: List<JCExpression> thrown
         List<JCExpression> arg5 = List.<JCExpression>nil();
	 if (n.getThrows() != null) {
	    for (final NameExpr name : n.getThrows()) {
	       arg5 = arg5.append( (JCExpression) name.accept(this, arg));
	    }
	 }

         //ARG6: JCBlock body
         JCBlock arg6 = null;
	 if (n.getBody() != null) {
	    arg6 = (JCBlock) n.getBody().accept(this, arg);
	 }

         //ARG7: JCExpression defaultValue
         // TODO - Must check where to get this
         JCExpression arg7 = null;

	 return new AJCMethodDecl( make.MethodDef( arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final NameExpr n, final Object arg) {
         //ARG0: Name name
         Name arg0 = names.fromString(n.getName());

	 return new AJCIdent( make.Ident( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final NormalAnnotationExpr n, final Object arg) {
         /* TODO - Not supporting annotations
	 JCTree result = n.getName().accept(this, arg);
	 if (n.getPairs() != null) {
	    for (final MemberValuePair m : n.getPairs()) {
	       JCTree result = m.accept(this, arg);
	    }
	 }
	 return new AJCNormalAnnotation( make.NormalAnnotation( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final NullLiteralExpr n, final Object arg) {
         //ARG0: int tag 
         int arg0 = TypeTags.BOT;
         
         //ARG1: Object value
         Object arg1 = null;

	 return new AJCLiteral( make.Literal( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ObjectCreationExpr n, final Object arg) {
         //ARG0: JCExpression encl
         JCExpression arg0 = null;
	 if (n.getScope() != null) {
	       arg0 = (JCExpression) n.getScope().accept(this, arg);
	 }

         //ARG1: List<JCExpression> typeargs
         List<JCExpression> arg1 = List.<JCExpression>nil();
	 if (n.getTypeArgs() != null) {
	    for (final com.github.javaparser.ast.type.Type t : n.getTypeArgs()) {
		  arg1 = arg1.append( (JCExpression) t.accept(this, arg));
	    }
	 }

         //ARG2: JCExpression clazz
	 JCExpression arg2 = (JCExpression) n.getType().accept(this, arg);

         //ARG3: List<JCExpression> args
         List<JCExpression> arg3 = List.<JCExpression>nil();
	 if (n.getArgs() != null) {
	    for (final Expression e : n.getArgs()) {
		  arg3 = arg3.append( (JCExpression) e.accept(this, arg));
	    }
	 }

         //ARG4: JCClassDecl def
         JCClassDecl arg4 = null;

         // Must convert internal modifiers
	 if (n.getAnonymousClassBody() != null) {
            long jcmodifier = 0;
            List<JCTree> defs = List.<JCTree>nil();
            
	    for (final BodyDeclaration member : n.getAnonymousClassBody()) {
               defs = defs.append (member.accept(this, arg));
               // TODO - Currently the modifier flags are accumulating
               // Must figure out how to separe them per class body
               if (member instanceof TypeDeclaration) jcmodifier = setJCTreeModifiers( ((TypeDeclaration) member).getModifiers(), jcmodifier);
	    }
            JCModifiers mods = new AJCModifiers( make.Modifiers( jcmodifier), null);
            arg4 = new AJCClassDecl( make.AnonymousClassDef(mods, defs), null);
	 }  


	 return new AJCNewClass( make.NewClass( arg0, arg1, arg2, arg3, arg4), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final PackageDeclaration n, final Object arg) {
         //ARG0: JCExpression
         // It returns a full qualified name
         JCExpression arg0 = (JCExpression) n.getName().accept(this, arg);

         /* TODO - Not supporting annotations
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */
         
         if (arg0 instanceof JCIdent) {
	    return new AJCIdent( (JCIdent) arg0, ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         }

	 return new AJCFieldAccess( (JCFieldAccess) arg0, ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final Parameter n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         //ARG1: Name name
	 //JCTree result = n.getId().accept(this, arg);
         Name arg1 = names.fromString(n.getId().getName());

         //ARG2: JCExpression vartype
	 JCExpression arg2 = (JCExpression) n.getType().accept(this, arg);

         //ARG3: JCExpression init
         // TODO - There is not such field in Java Parser
         JCExpression arg3 = null;

         /* TODO - annotations not supported
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */

	 return new AJCVariableDecl( make.VarDef( arg0, arg1, arg2, arg3), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final MultiTypeParameter n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0;
         long jcmodifier = setJCTreeModifiers( n.getModifiers(), 0);
         arg0 = new AJCModifiers( make.Modifiers( jcmodifier), null);

         /* TODO - Not supported yet
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
         }
         */
        
         //ARG1: Name name
         Name arg1 = names.fromString( n.getId().getName());

         //ARG2: JCExpression vartype
	 JCExpression arg2;
         if ( n.getTypes().size() > 1) {
            List<JCExpression> typelist = List.<JCExpression>nil();
	    for (final com.github.javaparser.ast.type.Type type : n.getTypes()) {
	       typelist = typelist.append( (JCExpression) type.accept(this, arg));
	    }
            arg2 = new AJCTypeUnion( make.TypeUnion(typelist), null);
         } else {
            // Get the single element
            arg2 = (JCExpression) n.getTypes().get(0).accept(this, arg);
         }

	 
         //ARG3: JCExpression init
         JCExpression arg3 = null;

	 return new AJCVariableDecl( make.VarDef( arg0, arg1, arg2, arg3 ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final PrimitiveType n, final Object arg) {
         //ARG0 Type t
         // t.tag is an int that contains the type code,
         // which in turn is defined at code/TypeTags
         int arg0;
         switch (n.getType()) {
            case Boolean: arg0 = TypeTags.BOOLEAN; break;
            case Char:    arg0 = TypeTags.CHAR; break;
            case Byte:    arg0 = TypeTags.BYTE; break;
            case Short:   arg0 = TypeTags.SHORT; break;
            case Int:     arg0 = TypeTags.INT; break;
            case Long:    arg0 = TypeTags.LONG; break;
            case Float:   arg0 = TypeTags.FLOAT; break;
            case Double:  arg0 = TypeTags.DOUBLE; break;
            default:      arg0 = TypeTags.UNKNOWN; break;
         }

	 return new AJCPrimitiveTypeTree( make.TypeIdent( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final QualifiedNameExpr n, final Object arg) {
         //ARG0: JCExpression selected
         JCExpression arg0 = (JCExpression) n.getQualifier().accept(this, arg);

         //ARG1: Name selector
	 Name arg1 = names.fromString( n.getName());

	 return new AJCFieldAccess( make.Select( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ReferenceType n, final Object arg) {
         // ARG0: JCExpression elemtype
         // array type
	 JCExpression arg0 = (JCExpression) n.getType().accept(this, arg);

         // Check if not array -
         // Right now just returning the type created elsewhere, but discarding comments.
         // TODO - Check if such comments are necessary
         if (n.getArrayCount() < 1) return arg0;

         //  Add the n-1 dimentions - The last one is assumed by the ArrayType
         for (int i = 0; i < (n.getArrayCount()-1); i++) {
            arg0 = new AJCArrayTypeTree( make.TypeArray( arg0), null);
         }

	 return new AJCArrayTypeTree(  make.TypeArray( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ReturnStmt n, final Object arg) {
         //ARG0: JCExpression expr
         JCExpression arg0 = null;
	 if (n.getExpr() != null) {
	       arg0 = (JCExpression) n.getExpr().accept(this, arg);
	 }

	 return new AJCReturn( make.Return( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final SingleMemberAnnotationExpr n, final Object arg) {
         /*
         TODO - Not processing annotations
	 JCTree result = n.getName().accept(this, arg);
	 JCTree result = n.getMemberValue().accept(this, arg);
	 return new AJCSingleMemberAnnotation( make.SingleMemberAnnotation( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final StringLiteralExpr n, final Object arg) {
         //ARG0: Object value
         String arg0 =  new String( n.getValue());

	 return new AJCLiteral( make.Literal( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final SuperExpr n, final Object arg) {
         //ARG0: JCExpression selected
         JCExpression arg0;

         //ARG1: Name selector
         Name arg1 = names.names._super;

	 if (n.getClassExpr() == null) {
            return new AJCIdent( make.Ident( arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         }

	 arg0 = (JCExpression) n.getClassExpr().accept(this, arg);

	 return new AJCFieldAccess( make.Select( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final SwitchEntryStmt n, final Object arg) {
         //ARG0: JCExpression pat
         JCExpression arg0 = null;
	 if (n.getLabel() != null) {
	    arg0 = (JCExpression) n.getLabel().accept(this, arg);
	 }

         //ARG1: List<JCStatement> stats
         List<JCStatement> arg1 = List.<JCStatement>nil();
	 if (n.getStmts() != null) {
	    for (final Statement s : n.getStmts()) {
	       arg1 = arg1.append( (JCStatement) s.accept(this, arg));
	    }
	 }

	 return new AJCCase( make.Case( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final SwitchStmt n, final Object arg) {
	 //ARG0: JCExpression selector
	 JCExpression arg0 = (JCExpression) n.getSelector().accept(this, arg);

	 //ARG1: List<JCCase> cases
         List<JCCase> arg1 = List.<JCCase>nil();
	 if (n.getEntries() != null) {
	    for (final SwitchEntryStmt e : n.getEntries()) {
	       arg1 = arg1.append( (JCCase) e.accept(this, arg));
	    }
	 }

	 return new AJCSwitch( make.Switch( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );

      }

   @Override
      public JCTree visit(final SynchronizedStmt n, final Object arg) {
	 //ARG0: JCExpression lock
	 JCExpression arg0 = null;
	 if (n.getExpr() != null) {
	    arg0 = (JCExpression) n.getExpr().accept(this, arg);
	 }

	 //ARG0: JCBlock body
	 JCBlock arg1 = (JCBlock) n.getBlock().accept(this, arg);

	 return new AJCSynchronized( make.Synchronized( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ThisExpr n, final Object arg) {
         //ARG0: JCExpression selected
         JCExpression arg0;

         //ARG1: Name selector
         Name arg1 = names.names._this;

	 if (n.getClassExpr() == null) {
            return new AJCIdent( make.Ident( arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         }
	 arg0 = (JCExpression) n.getClassExpr().accept(this, arg);

	 return new AJCFieldAccess( make.Select( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final ThrowStmt n, final Object arg) {
	 // ARG0: JCTree expr
	 JCTree arg0 = n.getExpr().accept(this, arg);

	 return new AJCThrow( make.Throw( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final TryStmt n, final Object arg) {
	 //ARG0: List<JCTree> resources 
	 List<JCTree> arg0 = List.<JCTree>nil();
	 if (n.getResources() != null) {
	    for (final VariableDeclarationExpr v : n.getResources()) {
	       // TODO - Currently not supporting multiple var declaration per line
	       arg0 = arg0.append( (JCTree) v.accept(this, arg));
	    }
	 }

	 //ARG1: JCBlock body
	 JCBlock arg1 = (JCBlock) n.getTryBlock().accept(this, arg);

	 //ARG2: List<JCCatch> catchers
	 List<JCCatch> arg2 = List.<JCCatch>nil();
	 if (n.getCatchs() != null) {
	    for (final CatchClause c : n.getCatchs()) {
	       arg2 = arg2.append( (JCCatch) c.accept(this, arg));
	    }
	 }

	 //ARG3: JCBlock finalizer
	 JCBlock arg3 = null;
	 if (n.getFinallyBlock() != null) {
	    arg3 = (JCBlock) n.getFinallyBlock().accept(this, arg);
	 }

	 return new AJCTry( make.Try(arg0, arg1, arg2, arg3), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final TypeDeclarationStmt n, final Object arg) {
         /* TODO - Must figure out how to return a type declaration as a statement
	 JCTree result = n.getTypeDeclaration().accept(this, arg);
	 return new AJCTypeDeclaration( make.ClassDef( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final TypeParameter n, final Object arg) {
         //ARG0: Name name
         Name arg0 = names.fromString(n.getName());

         //ARG1: List<JCExpression> bounds
         List<JCExpression> arg1 = List.<JCExpression>nil();
	 if (n.getTypeBound() != null) {
	    for (final ClassOrInterfaceType c : n.getTypeBound()) {
		  arg1 = arg1.append( (JCExpression) c.accept(this, arg));
	    }
	 }
	 return new AJCTypeParameter( make.TypeParameter( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final UnaryExpr n, final Object arg) {
         // ARG0: int opcode
	 int arg0;
         switch( n.getOperator() ) {
            case positive:     arg0 = JCTree.POS; break;
            case negative:     arg0 = JCTree.NEG; break;
            case preIncrement: arg0 = JCTree.PREINC; break;
            case preDecrement: arg0 = JCTree.PREDEC; break;
            case not:          arg0 = JCTree.NOT; break;
            case inverse:      arg0 = JCTree.COMPL; break;
            case posIncrement: arg0 = JCTree.POSTINC; break;
            case posDecrement: arg0 = JCTree.POSTDEC; break;
            default:           arg0 = JCTree.ERRONEOUS;
         }

         // ARG1: JCExpression arg
	 JCExpression arg1 = (JCExpression) n.getExpr().accept(this, arg);

	 return new AJCUnary( make.Unary( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final UnknownType n, final Object arg) {
         //ARG0 int
         // An unknown type is a primitive type idetified
         // by label defined in code/TypeTags
         int arg0 = TypeTags.UNKNOWN;

	 return new AJCPrimitiveTypeTree( make.TypeIdent(arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final VariableDeclarationExpr n, final Object arg) {
         //ARG0: JCModifiers mods
         JCModifiers arg0 = new AJCModifiers( make.Modifiers( setJCTreeModifiers( n.getModifiers(), 0)), null);

         //ARG1: Name name
         Name arg1 = null;

         //ARG2: JCExpression vartype
         JCExpression arg2 = (JCExpression) n.getType().accept(this, arg);

         //ARG3: JCExpression init
         JCExpression arg3 = null;

         /*
	 if (n.getAnnotations() != null) {
	    for (final AnnotationExpr a : n.getAnnotations()) {
		  JCTree result = a.accept(this, arg);
	    }
	 }
         */

         // Multiple variable declarations per line are not supported.
         // Currently only last declaration is preserved.
         // We assume that ComplyJCVisitor has called before to unfold the multiple declarataions.
	 for (final VariableDeclarator v : n.getVars()) {
               arg1 = names.fromString( v.getId().getName());
               if (v.getInit() != null) {
                  arg3 = (JCExpression) v.getInit().accept(this, arg);
               } else {
                  arg3 = null;
               }
	 }

	 return new AJCVariableDecl( make.VarDef( arg0, arg1, arg2, arg3), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final VariableDeclarator n, final Object arg) {
         /* Should not process this element
	 JCTree result = n.getId().accept(this, arg);
	 if (n.getInit() != null) {
	       JCTree result = n.getInit().accept(this, arg);
	 }

	 return new AJCVariableDeclarator( make.VariableDeclarator( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final VariableDeclaratorId n, final Object arg) {
         //ARG0: Name name
         Name arg0 = names.fromString( n.getName());

	 return new AJCIdent( make.Ident( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final VoidType n, final Object arg) {
         //ARG0: int
         // Void is treated as primitive type in JCTree
         int arg0 = TypeTags.VOID;

	 return new AJCPrimitiveTypeTree( make.TypeIdent( arg0), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final WhileStmt n, final Object arg) {
         //ARG0: JCExpression cond
	 JCExpression arg0 = (JCExpression) n.getCondition().accept(this, arg);

         //ARG0: JCStatement body
	 JCStatement arg1 = (JCStatement) n.getBody().accept(this, arg);

	 return new AJCWhileLoop( make.WhileLoop( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(final WildcardType n, final Object arg) {
         //ARG0: TypeBoundKind kind
         // For < ? extends>  or < ? super > or < ? >
         TypeBoundKind arg0;

         //ARG1: JCTree inner
         // A class associated to this type, if any
         JCTree arg1;

	 if (n.getExtends() != null) {
               arg0 = new ATypeBoundKind( make.TypeBoundKind(EXTENDS), null); 
	       arg1 = n.getExtends().accept(this, arg);
	 } else if (n.getSuper() != null) {
               arg0 = new ATypeBoundKind( make.TypeBoundKind(SUPER), null); 
	       arg1 = n.getSuper().accept(this, arg);
	 } else {
               arg0 = new ATypeBoundKind( make.TypeBoundKind(UNBOUND), null); 
	       arg1 = null;
         }

	 return new AJCWildcard( make.Wildcard( arg0, arg1), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
      }

   @Override
      public JCTree visit(LambdaExpr n, Object arg) {
         /* TODO - Check how to translate
	 return new AJCn,( make.n,( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(MethodReferenceExpr n, Object arg){
         /* TODO - Check how to translate
	 return new AJCn,( make.n,( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(TypeExpr n, Object arg){
         // TODO - Passing type "as is", since it should already be a JCIdent or JCFieldAccess
         //System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
	 return n.getType().accept(this, arg);
      }

   @Override
      public JCTree visit(final BlockComment n, final Object arg) {
         /* Doesn't have to visit the comment at this point
	 return new AJCBlockComment( make.BlockComment( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

   @Override
      public JCTree visit(final LineComment n, final Object arg) {
         /* Doesn't have to visit the comment at this point
	 return new AJCLineComment( make.LineComment( ), ( (n.getComment()!=null)?n.getComment().getContent():null ) );
         */
         System.err.println("Assigning null at:" + Thread.currentThread().getStackTrace()[1].getLineNumber()); return null;
      }

}
