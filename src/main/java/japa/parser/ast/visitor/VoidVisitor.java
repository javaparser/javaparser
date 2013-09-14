/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
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
 * Created on 05/10/2006
 */
package japa.parser.ast.visitor;

import japa.parser.ast.BlockComment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
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
import japa.parser.ast.body.MultiTypeParameter;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
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
import japa.parser.ast.type.VoidType;
import japa.parser.ast.type.WildcardType;

/**
 * A visitor that does not return anything.
 * 
 * @author Julio Vilmar Gesser
 */
public interface VoidVisitor<A> {

	//- Compilation Unit ----------------------------------

	void visit(CompilationUnit n, A arg);

	void visit(PackageDeclaration n, A arg);

	void visit(ImportDeclaration n, A arg);

	void visit(TypeParameter n, A arg);

	void visit(LineComment n, A arg);

	void visit(BlockComment n, A arg);

	//- Body ----------------------------------------------

	void visit(ClassOrInterfaceDeclaration n, A arg);

	void visit(EnumDeclaration n, A arg);

	void visit(EmptyTypeDeclaration n, A arg);

	void visit(EnumConstantDeclaration n, A arg);

	void visit(AnnotationDeclaration n, A arg);

	void visit(AnnotationMemberDeclaration n, A arg);

	void visit(FieldDeclaration n, A arg);

	void visit(VariableDeclarator n, A arg);

	void visit(VariableDeclaratorId n, A arg);

	void visit(ConstructorDeclaration n, A arg);

	void visit(MethodDeclaration n, A arg);

	void visit(Parameter n, A arg);
	
	void visit(MultiTypeParameter n, A arg);

	void visit(EmptyMemberDeclaration n, A arg);

	void visit(InitializerDeclaration n, A arg);

	void visit(JavadocComment n, A arg);

	//- Type ----------------------------------------------

	void visit(ClassOrInterfaceType n, A arg);

	void visit(PrimitiveType n, A arg);

	void visit(ReferenceType n, A arg);

	void visit(VoidType n, A arg);

	void visit(WildcardType n, A arg);

	//- Expression ----------------------------------------

	void visit(ArrayAccessExpr n, A arg);

	void visit(ArrayCreationExpr n, A arg);

	void visit(ArrayInitializerExpr n, A arg);

	void visit(AssignExpr n, A arg);

	void visit(BinaryExpr n, A arg);

	void visit(CastExpr n, A arg);

	void visit(ClassExpr n, A arg);

	void visit(ConditionalExpr n, A arg);

	void visit(EnclosedExpr n, A arg);

	void visit(FieldAccessExpr n, A arg);

	void visit(InstanceOfExpr n, A arg);

	void visit(StringLiteralExpr n, A arg);

	void visit(IntegerLiteralExpr n, A arg);

	void visit(LongLiteralExpr n, A arg);

	void visit(IntegerLiteralMinValueExpr n, A arg);

	void visit(LongLiteralMinValueExpr n, A arg);

	void visit(CharLiteralExpr n, A arg);

	void visit(DoubleLiteralExpr n, A arg);

	void visit(BooleanLiteralExpr n, A arg);

	void visit(NullLiteralExpr n, A arg);

	void visit(MethodCallExpr n, A arg);

	void visit(NameExpr n, A arg);

	void visit(ObjectCreationExpr n, A arg);

	void visit(QualifiedNameExpr n, A arg);

	void visit(ThisExpr n, A arg);

	void visit(SuperExpr n, A arg);

	void visit(UnaryExpr n, A arg);

	void visit(VariableDeclarationExpr n, A arg);

	void visit(MarkerAnnotationExpr n, A arg);

	void visit(SingleMemberAnnotationExpr n, A arg);

	void visit(NormalAnnotationExpr n, A arg);

	void visit(MemberValuePair n, A arg);

	//- Statements ----------------------------------------

	void visit(ExplicitConstructorInvocationStmt n, A arg);

	void visit(TypeDeclarationStmt n, A arg);

	void visit(AssertStmt n, A arg);

	void visit(BlockStmt n, A arg);

	void visit(LabeledStmt n, A arg);

	void visit(EmptyStmt n, A arg);

	void visit(ExpressionStmt n, A arg);

	void visit(SwitchStmt n, A arg);

	void visit(SwitchEntryStmt n, A arg);

	void visit(BreakStmt n, A arg);

	void visit(ReturnStmt n, A arg);

	void visit(IfStmt n, A arg);

	void visit(WhileStmt n, A arg);

	void visit(ContinueStmt n, A arg);

	void visit(DoStmt n, A arg);

	void visit(ForeachStmt n, A arg);

	void visit(ForStmt n, A arg);

	void visit(ThrowStmt n, A arg);

	void visit(SynchronizedStmt n, A arg);

	void visit(TryStmt n, A arg);

	void visit(CatchClause n, A arg);

}
