/*
 * Copyright (C) 2008 J�lio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 09/06/2008
 */
package japa.parser.ast.visitor;

import japa.parser.ast.BlockComment;
import japa.parser.ast.Comment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import japa.parser.ast.body.EmptyMemberDeclaration;
import japa.parser.ast.body.EmptyTypeDeclaration;
import japa.parser.ast.body.EnumConstantDeclaration;
import japa.parser.ast.body.EnumDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.InitializerDeclaration;
import japa.parser.ast.body.JavadocComment;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.expr.ArrayAccessExpr;
import japa.parser.ast.expr.ArrayCreationExpr;
import japa.parser.ast.expr.ArrayInitializerExpr;
import japa.parser.ast.expr.AssignExpr;
import japa.parser.ast.expr.BinaryExpr;
import japa.parser.ast.expr.BooleanLiteralExpr;
import japa.parser.ast.expr.CastExpr;
import japa.parser.ast.expr.CharLiteralExpr;
import japa.parser.ast.expr.ClassExpr;
import japa.parser.ast.expr.ConditionalExpr;
import japa.parser.ast.expr.DoubleLiteralExpr;
import japa.parser.ast.expr.EnclosedExpr;
import japa.parser.ast.expr.Expression;
import japa.parser.ast.expr.FieldAccessExpr;
import japa.parser.ast.expr.InstanceOfExpr;
import japa.parser.ast.expr.IntegerLiteralExpr;
import japa.parser.ast.expr.IntegerLiteralMinValueExpr;
import japa.parser.ast.expr.LongLiteralExpr;
import japa.parser.ast.expr.LongLiteralMinValueExpr;
import japa.parser.ast.expr.MarkerAnnotationExpr;
import japa.parser.ast.expr.MemberValuePair;
import japa.parser.ast.expr.MethodCallExpr;
import japa.parser.ast.expr.NameExpr;
import japa.parser.ast.expr.NormalAnnotationExpr;
import japa.parser.ast.expr.NullLiteralExpr;
import japa.parser.ast.expr.ObjectCreationExpr;
import japa.parser.ast.expr.QualifiedNameExpr;
import japa.parser.ast.expr.SingleMemberAnnotationExpr;
import japa.parser.ast.expr.StringLiteralExpr;
import japa.parser.ast.expr.SuperExpr;
import japa.parser.ast.expr.ThisExpr;
import japa.parser.ast.expr.UnaryExpr;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.AssertStmt;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.BreakStmt;
import japa.parser.ast.stmt.CatchClause;
import japa.parser.ast.stmt.ContinueStmt;
import japa.parser.ast.stmt.DoStmt;
import japa.parser.ast.stmt.EmptyStmt;
import japa.parser.ast.stmt.ExplicitConstructorInvocationStmt;
import japa.parser.ast.stmt.ExpressionStmt;
import japa.parser.ast.stmt.ForStmt;
import japa.parser.ast.stmt.ForeachStmt;
import japa.parser.ast.stmt.IfStmt;
import japa.parser.ast.stmt.LabeledStmt;
import japa.parser.ast.stmt.ReturnStmt;
import japa.parser.ast.stmt.Statement;
import japa.parser.ast.stmt.SwitchEntryStmt;
import japa.parser.ast.stmt.SwitchStmt;
import japa.parser.ast.stmt.SynchronizedStmt;
import japa.parser.ast.stmt.ThrowStmt;
import japa.parser.ast.stmt.TryStmt;
import japa.parser.ast.stmt.TypeDeclarationStmt;
import japa.parser.ast.stmt.WhileStmt;
import japa.parser.ast.type.ClassOrInterfaceType;
import japa.parser.ast.type.PrimitiveType;
import japa.parser.ast.type.ReferenceType;
import japa.parser.ast.type.Type;
import japa.parser.ast.type.VoidType;
import japa.parser.ast.type.WildcardType;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class VoidVisitorAdapter<A> implements VoidVisitor<A> {

    @Override public void visit(AnnotationDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getMembers() != null) {
            for (BodyDeclaration member : n.getMembers()) {
                member.accept(this, arg);
            }
        }
    }

    @Override public void visit(AnnotationMemberDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        if (n.getDefaultValue() != null) {
            n.getDefaultValue().accept(this, arg);
        }
    }

    @Override public void visit(ArrayAccessExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        n.getIndex().accept(this, arg);
    }

    @Override public void visit(ArrayCreationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
        if (n.getDimensions() != null) {
            for (Expression dim : n.getDimensions()) {
                dim.accept(this, arg);
            }
        } else {
            n.getInitializer().accept(this, arg);
        }
    }

    @Override public void visit(ArrayInitializerExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getValues() != null) {
            for (Expression expr : n.getValues()) {
                expr.accept(this, arg);
            }
        }
    }

    @Override public void visit(AssertStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getCheck().accept(this, arg);
        if (n.getMessage() != null) {
            n.getMessage().accept(this, arg);
        }
    }

    @Override public void visit(AssignExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getTarget().accept(this, arg);
        n.getValue().accept(this, arg);
    }

    @Override public void visit(BinaryExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getLeft().accept(this, arg);
        n.getRight().accept(this, arg);
    }

    @Override public void visit(BlockComment n, A arg) {
      visitComment(n.getComment(), arg);
    }

    @Override public void visit(BlockStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getStmts() != null) {
            for (Statement s : n.getStmts()) {
                s.accept(this, arg);
            }
        }
    }

    @Override public void visit(BooleanLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(BreakStmt n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(CastExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
        n.getExpr().accept(this, arg);
    }

    @Override public void visit(CatchClause n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExcept().accept(this, arg);
        n.getCatchBlock().accept(this, arg);
    }

    @Override public void visit(CharLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(ClassExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
    }

    @Override public void visit(ClassOrInterfaceDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getTypeParameters() != null) {
            for (TypeParameter t : n.getTypeParameters()) {
                t.accept(this, arg);
            }
        }
        if (n.getExtends() != null) {
            for (ClassOrInterfaceType c : n.getExtends()) {
                c.accept(this, arg);
            }
        }

        if (n.getImplements() != null) {
            for (ClassOrInterfaceType c : n.getImplements()) {
                c.accept(this, arg);
            }
        }
        if (n.getMembers() != null) {
            for (BodyDeclaration member : n.getMembers()) {
                member.accept(this, arg);
            }
        }
    }

    @Override public void visit(ClassOrInterfaceType n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getScope() != null) {
            n.getScope().accept(this, arg);
        }
        if (n.getTypeArgs() != null) {
            for (Type t : n.getTypeArgs()) {
                t.accept(this, arg);
            }
        }
    }

    @Override public void visit(CompilationUnit n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getPackage() != null) {
            n.getPackage().accept(this, arg);
        }
        if (n.getImports() != null) {
            for (ImportDeclaration i : n.getImports()) {
                i.accept(this, arg);
            }
        }
        if (n.getTypes() != null) {
            for (TypeDeclaration typeDeclaration : n.getTypes()) {
                typeDeclaration.accept(this, arg);
            }
        }
    }

    @Override public void visit(ConditionalExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getThenExpr().accept(this, arg);
        n.getElseExpr().accept(this, arg);
    }

    @Override public void visit(ConstructorDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getTypeParameters() != null) {
            for (TypeParameter t : n.getTypeParameters()) {
                t.accept(this, arg);
            }
        }
        if (n.getParameters() != null) {
            for (Parameter p : n.getParameters()) {
                p.accept(this, arg);
            }
        }
        if (n.getThrows() != null) {
            for (NameExpr name : n.getThrows()) {
                name.accept(this, arg);
            }
        }
        n.getBlock().accept(this, arg);
    }

    @Override public void visit(ContinueStmt n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(DoStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getBody().accept(this, arg);
        n.getCondition().accept(this, arg);
    }

    @Override public void visit(DoubleLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(EmptyMemberDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
    }

    @Override public void visit(EmptyStmt n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(EmptyTypeDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
    }

    @Override public void visit(EnclosedExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getInner().accept(this, arg);
    }

    @Override public void visit(EnumConstantDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getArgs() != null) {
            for (Expression e : n.getArgs()) {
                e.accept(this, arg);
            }
        }
        if (n.getClassBody() != null) {
            for (BodyDeclaration member : n.getClassBody()) {
                member.accept(this, arg);
            }
        }
    }

    @Override public void visit(EnumDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getImplements() != null) {
            for (ClassOrInterfaceType c : n.getImplements()) {
                c.accept(this, arg);
            }
        }
        if (n.getEntries() != null) {
            for (EnumConstantDeclaration e : n.getEntries()) {
                e.accept(this, arg);
            }
        }
        if (n.getMembers() != null) {
            for (BodyDeclaration member : n.getMembers()) {
                member.accept(this, arg);
            }
        }
    }

    @Override public void visit(ExplicitConstructorInvocationStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        if (!n.isThis()) {
            if (n.getExpr() != null) {
                n.getExpr().accept(this, arg);
            }
        }
        if (n.getTypeArgs() != null) {
            for (Type t : n.getTypeArgs()) {
                t.accept(this, arg);
            }
        }
        if (n.getArgs() != null) {
            for (Expression e : n.getArgs()) {
                e.accept(this, arg);
            }
        }
    }

    @Override public void visit(ExpressionStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
    }

    @Override public void visit(FieldAccessExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getScope().accept(this, arg);
    }

    @Override public void visit(FieldDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        for (VariableDeclarator var : n.getVariables()) {
            var.accept(this, arg);
        }
    }

    @Override public void visit(ForeachStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getVariable().accept(this, arg);
        n.getIterable().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override public void visit(ForStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getInit() != null) {
            for (Expression e : n.getInit()) {
                e.accept(this, arg);
            }
        }
        if (n.getCompare() != null) {
            n.getCompare().accept(this, arg);
        }
        if (n.getUpdate() != null) {
            for (Expression e : n.getUpdate()) {
                e.accept(this, arg);
            }
        }
        n.getBody().accept(this, arg);
    }

    @Override public void visit(IfStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getThenStmt().accept(this, arg);
        if (n.getElseStmt() != null) {
            n.getElseStmt().accept(this, arg);
        }
    }

    @Override public void visit(ImportDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
    }

    @Override public void visit(InitializerDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        n.getBlock().accept(this, arg);
    }

    @Override public void visit(InstanceOfExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExpr().accept(this, arg);
        n.getType().accept(this, arg);
    }

    @Override public void visit(IntegerLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(IntegerLiteralMinValueExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(JavadocComment n, A arg) {
      visitComment(n.getComment(), arg);
    }

    @Override public void visit(LabeledStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getStmt().accept(this, arg);
    }

    @Override public void visit(LineComment n, A arg) {
      visitComment(n.getComment(), arg);
    }

    @Override public void visit(LongLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(LongLiteralMinValueExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(MarkerAnnotationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
    }

    @Override public void visit(MemberValuePair n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getValue().accept(this, arg);
    }

    @Override public void visit(MethodCallExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getScope() != null) {
            n.getScope().accept(this, arg);
        }
        if (n.getTypeArgs() != null) {
            for (Type t : n.getTypeArgs()) {
                t.accept(this, arg);
            }
        }
        if (n.getArgs() != null) {
            for (Expression e : n.getArgs()) {
                e.accept(this, arg);
            }
        }
    }

    @Override public void visit(MethodDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getJavaDoc() != null) {
            n.getJavaDoc().accept(this, arg);
        }
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        if (n.getTypeParameters() != null) {
            for (TypeParameter t : n.getTypeParameters()) {
                t.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        if (n.getParameters() != null) {
            for (Parameter p : n.getParameters()) {
                p.accept(this, arg);
            }
        }
        if (n.getThrows() != null) {
            for (NameExpr name : n.getThrows()) {
                name.accept(this, arg);
            }
        }
        if (n.getBody() != null) {
            n.getBody().accept(this, arg);
        }
    }

    @Override public void visit(NameExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(NormalAnnotationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        if (n.getPairs() != null) {
            for (MemberValuePair m : n.getPairs()) {
                m.accept(this, arg);
            }
        }
    }

    @Override public void visit(NullLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(ObjectCreationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getScope() != null) {
            n.getScope().accept(this, arg);
        }
        if (n.getTypeArgs() != null) {
            for (Type t : n.getTypeArgs()) {
                t.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        if (n.getArgs() != null) {
            for (Expression e : n.getArgs()) {
                e.accept(this, arg);
            }
        }
        if (n.getAnonymousClassBody() != null) {
            for (BodyDeclaration member : n.getAnonymousClassBody()) {
                member.accept(this, arg);
            }
        }
    }

    @Override public void visit(PackageDeclaration n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        n.getName().accept(this, arg);
    }

    @Override public void visit(Parameter n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        n.getId().accept(this, arg);
    }

    @Override public void visit(PrimitiveType n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(QualifiedNameExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getQualifier().accept(this, arg);
    }

    @Override public void visit(ReferenceType n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
    }

    @Override public void visit(ReturnStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getExpr() != null) {
            n.getExpr().accept(this, arg);
        }
    }

    @Override public void visit(SingleMemberAnnotationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        n.getMemberValue().accept(this, arg);
    }

    @Override public void visit(StringLiteralExpr n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(SuperExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getClassExpr() != null) {
            n.getClassExpr().accept(this, arg);
        }
    }

    @Override public void visit(SwitchEntryStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getLabel() != null) {
            n.getLabel().accept(this, arg);
        }
        if (n.getStmts() != null) {
            for (Statement s : n.getStmts()) {
                s.accept(this, arg);
            }
        }
    }

    @Override public void visit(SwitchStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getSelector().accept(this, arg);
        if (n.getEntries() != null) {
            for (SwitchEntryStmt e : n.getEntries()) {
                e.accept(this, arg);
            }
        }
    }

    @Override public void visit(SynchronizedStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExpr().accept(this, arg);
        n.getBlock().accept(this, arg);
    }

    @Override public void visit(ThisExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getClassExpr() != null) {
            n.getClassExpr().accept(this, arg);
        }
    }

    @Override public void visit(ThrowStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExpr().accept(this, arg);
    }

    @Override public void visit(TryStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getTryBlock().accept(this, arg);
        if (n.getCatchs() != null) {
            for (CatchClause c : n.getCatchs()) {
                c.accept(this, arg);
            }
        }
        if (n.getFinallyBlock() != null) {
            n.getFinallyBlock().accept(this, arg);
        }
    }

    @Override public void visit(TypeDeclarationStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getTypeDeclaration().accept(this, arg);
    }

    @Override public void visit(TypeParameter n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getTypeBound() != null) {
            for (ClassOrInterfaceType c : n.getTypeBound()) {
                c.accept(this, arg);
            }
        }
    }

    @Override public void visit(UnaryExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getExpr().accept(this, arg);
    }

    @Override public void visit(VariableDeclarationExpr n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getAnnotations() != null) {
            for (AnnotationExpr a : n.getAnnotations()) {
                a.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        for (VariableDeclarator v : n.getVars()) {
            v.accept(this, arg);
        }
    }

    @Override public void visit(VariableDeclarator n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getId().accept(this, arg);
        if (n.getInit() != null) {
            n.getInit().accept(this, arg);
        }
    }

    @Override public void visit(VariableDeclaratorId n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(VoidType n, A arg) {
    	visitComment(n.getComment(), arg);
    }

    @Override public void visit(WhileStmt n, A arg) {
    	visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override public void visit(WildcardType n, A arg) {
    	visitComment(n.getComment(), arg);
        if (n.getExtends() != null) {
            n.getExtends().accept(this, arg);
        }
        if (n.getSuper() != null) {
            n.getSuper().accept(this, arg);
        }
    }

    private void visitComment(Comment n, A arg) {
      if (n != null) {
         n.accept(this, arg);
      }
    }
}
