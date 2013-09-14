/*
 * Copyright (C) 2008 Júlio Vilmar Gesser.
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
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
import japa.parser.ast.body.BaseParameter;
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
import japa.parser.ast.body.MultiTypeParameter;
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

import java.util.LinkedList;
import java.util.List;

/**
 * This visitor adapter can be used to save time when some specific nodes needs
 * to be changed. To do that just extend this class and override the methods
 * from the nodes who needs to be changed, returning the changed node.
 * 
 * @author Julio Vilmar Gesser
 */
public abstract class ModifierVisitorAdapter<A> implements GenericVisitor<Node, A> {

	private void removeNulls(final List<?> list) {
		for (int i = list.size() - 1; i >= 0; i--) {
			if (list.get(i) == null) {
				list.remove(i);
			}
		}
	}

	@Override public Node visit(final AnnotationDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<BodyDeclaration> members = n.getMembers();
		if (members != null) {
			for (int i = 0; i < members.size(); i++) {
				members.set(i, (BodyDeclaration) members.get(i).accept(this, arg));
			}
			removeNulls(members);
		}
		return n;
	}

	@Override public Node visit(final AnnotationMemberDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		n.setType((Type) n.getType().accept(this, arg));
		if (n.getDefaultValue() != null) {
			n.setDefaultValue((Expression) n.getDefaultValue().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ArrayAccessExpr n, final A arg) {
		n.setName((Expression) n.getName().accept(this, arg));
		n.setIndex((Expression) n.getIndex().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ArrayCreationExpr n, final A arg) {
		n.setType((Type) n.getType().accept(this, arg));
		if (n.getDimensions() != null) {
			final List<Expression> dimensions = n.getDimensions();
			if (dimensions != null) {
				for (int i = 0; i < dimensions.size(); i++) {
					dimensions.set(i, (Expression) dimensions.get(i).accept(this, arg));
				}
				removeNulls(dimensions);
			}
		} else {
			n.setInitializer((ArrayInitializerExpr) n.getInitializer().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ArrayInitializerExpr n, final A arg) {
		if (n.getValues() != null) {
			final List<Expression> values = n.getValues();
			if (values != null) {
				for (int i = 0; i < values.size(); i++) {
					values.set(i, (Expression) values.get(i).accept(this, arg));
				}
				removeNulls(values);
			}
		}
		return n;
	}

	@Override public Node visit(final AssertStmt n, final A arg) {
		n.setCheck((Expression) n.getCheck().accept(this, arg));
		if (n.getMessage() != null) {
			n.setMessage((Expression) n.getMessage().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final AssignExpr n, final A arg) {
		n.setTarget((Expression) n.getTarget().accept(this, arg));
		n.setValue((Expression) n.getValue().accept(this, arg));
		return n;
	}

	@Override public Node visit(final BinaryExpr n, final A arg) {
		n.setLeft((Expression) n.getLeft().accept(this, arg));
		n.setRight((Expression) n.getRight().accept(this, arg));
		return n;
	}

	@Override public Node visit(final BlockStmt n, final A arg) {
		final List<Statement> stmts = n.getStmts();
		if (stmts != null) {
			for (int i = 0; i < stmts.size(); i++) {
				stmts.set(i, (Statement) stmts.get(i).accept(this, arg));
			}
			removeNulls(stmts);
		}
		return n;
	}

	@Override public Node visit(final BooleanLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final BreakStmt n, final A arg) {
		return n;
	}

	@Override public Node visit(final CastExpr n, final A arg) {
		n.setType((Type) n.getType().accept(this, arg));
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final CatchClause n, final A arg) {
		n.setExcept((MultiTypeParameter) n.getExcept().accept(this, arg));
		n.setCatchBlock((BlockStmt) n.getCatchBlock().accept(this, arg));
		return n;

	}

	@Override public Node visit(final CharLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final ClassExpr n, final A arg) {
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ClassOrInterfaceDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<TypeParameter> typeParameters = n.getTypeParameters();
		if (typeParameters != null) {
			for (int i = 0; i < typeParameters.size(); i++) {
				typeParameters.set(i, (TypeParameter) typeParameters.get(i).accept(this, arg));
			}
			removeNulls(typeParameters);
		}
		final List<ClassOrInterfaceType> extendz = n.getExtends();
		if (extendz != null) {
			for (int i = 0; i < extendz.size(); i++) {
				extendz.set(i, (ClassOrInterfaceType) extendz.get(i).accept(this, arg));
			}
			removeNulls(extendz);
		}
		final List<ClassOrInterfaceType> implementz = n.getImplements();
		if (implementz != null) {
			for (int i = 0; i < implementz.size(); i++) {
				implementz.set(i, (ClassOrInterfaceType) implementz.get(i).accept(this, arg));
			}
			removeNulls(implementz);
		}
		final List<BodyDeclaration> members = n.getMembers();
		if (members != null) {
			for (int i = 0; i < members.size(); i++) {
				members.set(i, (BodyDeclaration) members.get(i).accept(this, arg));
			}
			removeNulls(members);
		}
		return n;
	}

	@Override public Node visit(final ClassOrInterfaceType n, final A arg) {
		if (n.getScope() != null) {
			n.setScope((ClassOrInterfaceType) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgs = n.getTypeArgs();
		if (typeArgs != null) {
			for (int i = 0; i < typeArgs.size(); i++) {
				typeArgs.set(i, (Type) typeArgs.get(i).accept(this, arg));
			}
			removeNulls(typeArgs);
		}
		return n;
	}

	@Override public Node visit(final CompilationUnit n, final A arg) {
		if (n.getPackage() != null) {
			n.setPackage((PackageDeclaration) n.getPackage().accept(this, arg));
		}
		final List<ImportDeclaration> imports = n.getImports();
		if (imports != null) {
			for (int i = 0; i < imports.size(); i++) {
				imports.set(i, (ImportDeclaration) imports.get(i).accept(this, arg));
			}
			removeNulls(imports);
		}
		final List<TypeDeclaration> types = n.getTypes();
		if (types != null) {
			for (int i = 0; i < types.size(); i++) {
				types.set(i, (TypeDeclaration) types.get(i).accept(this, arg));
			}
			removeNulls(types);
		}
		return n;
	}

	@Override public Node visit(final ConditionalExpr n, final A arg) {
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		n.setThenExpr((Expression) n.getThenExpr().accept(this, arg));
		n.setElseExpr((Expression) n.getElseExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ConstructorDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<TypeParameter> typeParameters = n.getTypeParameters();
		if (typeParameters != null) {
			for (int i = 0; i < typeParameters.size(); i++) {
				typeParameters.set(i, (TypeParameter) typeParameters.get(i).accept(this, arg));
			}
			removeNulls(typeParameters);
		}
		final List<Parameter> parameters = n.getParameters();
		if (parameters != null) {
			for (int i = 0; i < parameters.size(); i++) {
				parameters.set(i, (Parameter) parameters.get(i).accept(this, arg));
			}
			removeNulls(parameters);
		}
		final List<NameExpr> throwz = n.getThrows();
		if (throwz != null) {
			for (int i = 0; i < throwz.size(); i++) {
				throwz.set(i, (NameExpr) throwz.get(i).accept(this, arg));
			}
			removeNulls(throwz);
		}
		n.setBlock((BlockStmt) n.getBlock().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ContinueStmt n, final A arg) {
		return n;
	}

	@Override public Node visit(final DoStmt n, final A arg) {
		n.setBody((Statement) n.getBody().accept(this, arg));
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		return n;
	}

	@Override public Node visit(final DoubleLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final EmptyMemberDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final EmptyStmt n, final A arg) {
		return n;
	}

	@Override public Node visit(final EmptyTypeDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final EnclosedExpr n, final A arg) {
		n.setInner((Expression) n.getInner().accept(this, arg));
		return n;
	}

	@Override public Node visit(final EnumConstantDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<Expression> args = n.getArgs();
		if (args != null) {
			for (int i = 0; i < args.size(); i++) {
				args.set(i, (Expression) args.get(i).accept(this, arg));
			}
			removeNulls(args);
		}
		final List<BodyDeclaration> classBody = n.getClassBody();
		if (classBody != null) {
			for (int i = 0; i < classBody.size(); i++) {
				classBody.set(i, (BodyDeclaration) classBody.get(i).accept(this, arg));
			}
			removeNulls(classBody);
		}
		return n;
	}

	@Override public Node visit(final EnumDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<ClassOrInterfaceType> implementz = n.getImplements();
		if (implementz != null) {
			for (int i = 0; i < implementz.size(); i++) {
				implementz.set(i, (ClassOrInterfaceType) implementz.get(i).accept(this, arg));
			}
			removeNulls(implementz);
		}
		final List<EnumConstantDeclaration> entries = n.getEntries();
		if (entries != null) {
			for (int i = 0; i < entries.size(); i++) {
				entries.set(i, (EnumConstantDeclaration) entries.get(i).accept(this, arg));
			}
			removeNulls(entries);
		}
		final List<BodyDeclaration> members = n.getMembers();
		if (members != null) {
			for (int i = 0; i < members.size(); i++) {
				members.set(i, (BodyDeclaration) members.get(i).accept(this, arg));
			}
			removeNulls(members);
		}
		return n;
	}

	@Override public Node visit(final ExplicitConstructorInvocationStmt n, final A arg) {
		if (!n.isThis()) {
			if (n.getExpr() != null) {
				n.setExpr((Expression) n.getExpr().accept(this, arg));
			}
		}
		final List<Type> typeArgs = n.getTypeArgs();
		if (typeArgs != null) {
			for (int i = 0; i < typeArgs.size(); i++) {
				typeArgs.set(i, (Type) typeArgs.get(i).accept(this, arg));
			}
			removeNulls(typeArgs);
		}
		final List<Expression> args = n.getArgs();
		if (args != null) {
			for (int i = 0; i < args.size(); i++) {
				args.set(i, (Expression) args.get(i).accept(this, arg));
			}
			removeNulls(args);
		}
		return n;
	}

	@Override public Node visit(final ExpressionStmt n, final A arg) {
		n.setExpression((Expression) n.getExpression().accept(this, arg));
		return n;
	}

	@Override public Node visit(final FieldAccessExpr n, final A arg) {
		n.setScope((Expression) n.getScope().accept(this, arg));
		return n;
	}

	@Override public Node visit(final FieldDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		n.setType((Type) n.getType().accept(this, arg));
		final List<VariableDeclarator> variables = n.getVariables();
		for (int i = 0; i < variables.size(); i++) {
			variables.set(i, (VariableDeclarator) variables.get(i).accept(this, arg));
		}
		removeNulls(variables);
		return n;
	}

	@Override public Node visit(final ForeachStmt n, final A arg) {
		n.setVariable((VariableDeclarationExpr) n.getVariable().accept(this, arg));
		n.setIterable((Expression) n.getIterable().accept(this, arg));
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ForStmt n, final A arg) {
		final List<Expression> init = n.getInit();
		if (init != null) {
			for (int i = 0; i < init.size(); i++) {
				init.set(i, (Expression) init.get(i).accept(this, arg));
			}
			removeNulls(init);
		}
		if (n.getCompare() != null) {
			n.setCompare((Expression) n.getCompare().accept(this, arg));
		}
		final List<Expression> update = n.getUpdate();
		if (update != null) {
			for (int i = 0; i < update.size(); i++) {
				update.set(i, (Expression) update.get(i).accept(this, arg));
			}
			removeNulls(update);
		}
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final IfStmt n, final A arg) {
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		n.setThenStmt((Statement) n.getThenStmt().accept(this, arg));
		if (n.getElseStmt() != null) {
			n.setElseStmt((Statement) n.getElseStmt().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ImportDeclaration n, final A arg) {
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}

	@Override public Node visit(final InitializerDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		n.setBlock((BlockStmt) n.getBlock().accept(this, arg));
		return n;
	}

	@Override public Node visit(final InstanceOfExpr n, final A arg) {
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

	@Override public Node visit(final IntegerLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final IntegerLiteralMinValueExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final JavadocComment n, final A arg) {
		return n;
	}

	@Override public Node visit(final LabeledStmt n, final A arg) {
		n.setStmt((Statement) n.getStmt().accept(this, arg));
		return n;
	}

	@Override public Node visit(final LongLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final LongLiteralMinValueExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final MarkerAnnotationExpr n, final A arg) {
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}

	@Override public Node visit(final MemberValuePair n, final A arg) {
		n.setValue((Expression) n.getValue().accept(this, arg));
		return n;
	}

	@Override public Node visit(final MethodCallExpr n, final A arg) {
		if (n.getScope() != null) {
			n.setScope((Expression) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgs = n.getTypeArgs();
		if (typeArgs != null) {
			for (int i = 0; i < typeArgs.size(); i++) {
				typeArgs.set(i, (Type) typeArgs.get(i).accept(this, arg));
			}
			removeNulls(typeArgs);
		}
		final List<Expression> args = n.getArgs();
		if (args != null) {
			for (int i = 0; i < args.size(); i++) {
				args.set(i, (Expression) args.get(i).accept(this, arg));
			}
			removeNulls(args);
		}
		return n;
	}

	@Override public Node visit(final MethodDeclaration n, final A arg) {
		if (n.getJavaDoc() != null) {
			n.setJavaDoc((JavadocComment) n.getJavaDoc().accept(this, arg));
		}
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		final List<TypeParameter> typeParameters = n.getTypeParameters();
		if (typeParameters != null) {
			for (int i = 0; i < typeParameters.size(); i++) {
				typeParameters.set(i, (TypeParameter) typeParameters.get(i).accept(this, arg));
			}
			removeNulls(typeParameters);
		}
		n.setType((Type) n.getType().accept(this, arg));
		final List<Parameter> parameters = n.getParameters();
		if (parameters != null) {
			for (int i = 0; i < parameters.size(); i++) {
				parameters.set(i, (Parameter) parameters.get(i).accept(this, arg));
			}
			removeNulls(parameters);
		}
		final List<NameExpr> throwz = n.getThrows();
		if (throwz != null) {
			for (int i = 0; i < throwz.size(); i++) {
				throwz.set(i, (NameExpr) throwz.get(i).accept(this, arg));
			}
			removeNulls(throwz);
		}
		if (n.getBody() != null) {
			n.setBody((BlockStmt) n.getBody().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final NameExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final NormalAnnotationExpr n, final A arg) {
		n.setName((NameExpr) n.getName().accept(this, arg));
		final List<MemberValuePair> pairs = n.getPairs();
		if (pairs != null) {
			for (int i = 0; i < pairs.size(); i++) {
				pairs.set(i, (MemberValuePair) pairs.get(i).accept(this, arg));
			}
			removeNulls(pairs);
		}
		return n;
	}

	@Override public Node visit(final NullLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final ObjectCreationExpr n, final A arg) {
		if (n.getScope() != null) {
			n.setScope((Expression) n.getScope().accept(this, arg));
		}
		final List<Type> typeArgs = n.getTypeArgs();
		if (typeArgs != null) {
			for (int i = 0; i < typeArgs.size(); i++) {
				typeArgs.set(i, (Type) typeArgs.get(i).accept(this, arg));
			}
			removeNulls(typeArgs);
		}
		n.setType((ClassOrInterfaceType) n.getType().accept(this, arg));
		final List<Expression> args = n.getArgs();
		if (args != null) {
			for (int i = 0; i < args.size(); i++) {
				args.set(i, (Expression) args.get(i).accept(this, arg));
			}
			removeNulls(args);
		}
		final List<BodyDeclaration> anonymousClassBody = n.getAnonymousClassBody();
		if (anonymousClassBody != null) {
			for (int i = 0; i < anonymousClassBody.size(); i++) {
				anonymousClassBody.set(i, (BodyDeclaration) anonymousClassBody.get(i).accept(this, arg));
			}
			removeNulls(anonymousClassBody);
		}
		return n;
	}

	@Override public Node visit(final PackageDeclaration n, final A arg) {
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		n.setName((NameExpr) n.getName().accept(this, arg));
		return n;
	}
	
	@Override public Node visit(final Parameter n, final A arg) {
		visit((BaseParameter) n, arg);
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}
	
	public Node visit(MultiTypeParameter n, A arg) {
    	visit((BaseParameter) n, arg);
    	List<Type> types = new LinkedList<Type>();
    	for (Type type : n.getTypes()) {
    		types.add((Type) type.accept(this, arg));
    	}
        n.setTypes(types);
        return n;
    }

	protected Node visit(final BaseParameter n, final A arg) {
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		
		n.setId((VariableDeclaratorId) n.getId().accept(this, arg));
		return n;
	}

	@Override public Node visit(final PrimitiveType n, final A arg) {
		return n;
	}

	@Override public Node visit(final QualifiedNameExpr n, final A arg) {
		n.setQualifier((NameExpr) n.getQualifier().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ReferenceType n, final A arg) {
		n.setType((Type) n.getType().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ReturnStmt n, final A arg) {
		if (n.getExpr() != null) {
			n.setExpr((Expression) n.getExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final SingleMemberAnnotationExpr n, final A arg) {
		n.setName((NameExpr) n.getName().accept(this, arg));
		n.setMemberValue((Expression) n.getMemberValue().accept(this, arg));
		return n;
	}

	@Override public Node visit(final StringLiteralExpr n, final A arg) {
		return n;
	}

	@Override public Node visit(final SuperExpr n, final A arg) {
		if (n.getClassExpr() != null) {
			n.setClassExpr((Expression) n.getClassExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final SwitchEntryStmt n, final A arg) {
		if (n.getLabel() != null) {
			n.setLabel((Expression) n.getLabel().accept(this, arg));
		}
		final List<Statement> stmts = n.getStmts();
		if (stmts != null) {
			for (int i = 0; i < stmts.size(); i++) {
				stmts.set(i, (Statement) stmts.get(i).accept(this, arg));
			}
			removeNulls(stmts);
		}
		return n;
	}

	@Override public Node visit(final SwitchStmt n, final A arg) {
		n.setSelector((Expression) n.getSelector().accept(this, arg));
		final List<SwitchEntryStmt> entries = n.getEntries();
		if (entries != null) {
			for (int i = 0; i < entries.size(); i++) {
				entries.set(i, (SwitchEntryStmt) entries.get(i).accept(this, arg));
			}
			removeNulls(entries);
		}
		return n;

	}

	@Override public Node visit(final SynchronizedStmt n, final A arg) {
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		n.setBlock((BlockStmt) n.getBlock().accept(this, arg));
		return n;
	}

	@Override public Node visit(final ThisExpr n, final A arg) {
		if (n.getClassExpr() != null) {
			n.setClassExpr((Expression) n.getClassExpr().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final ThrowStmt n, final A arg) {
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TryStmt n, final A arg) {
		n.setTryBlock((BlockStmt) n.getTryBlock().accept(this, arg));
		final List<CatchClause> catchs = n.getCatchs();
		if (catchs != null) {
			for (int i = 0; i < catchs.size(); i++) {
				catchs.set(i, (CatchClause) catchs.get(i).accept(this, arg));
			}
			removeNulls(catchs);
		}
		if (n.getFinallyBlock() != null) {
			n.setFinallyBlock((BlockStmt) n.getFinallyBlock().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final TypeDeclarationStmt n, final A arg) {
		n.setTypeDeclaration((TypeDeclaration) n.getTypeDeclaration().accept(this, arg));
		return n;
	}

	@Override public Node visit(final TypeParameter n, final A arg) {
		final List<ClassOrInterfaceType> typeBound = n.getTypeBound();
		if (typeBound != null) {
			for (int i = 0; i < typeBound.size(); i++) {
				typeBound.set(i, (ClassOrInterfaceType) typeBound.get(i).accept(this, arg));
			}
			removeNulls(typeBound);
		}
		return n;
	}

	@Override public Node visit(final UnaryExpr n, final A arg) {
		n.setExpr((Expression) n.getExpr().accept(this, arg));
		return n;
	}

	@Override public Node visit(final VariableDeclarationExpr n, final A arg) {
		final List<AnnotationExpr> annotations = n.getAnnotations();
		if (annotations != null) {
			for (int i = 0; i < annotations.size(); i++) {
				annotations.set(i, (AnnotationExpr) annotations.get(i).accept(this, arg));
			}
			removeNulls(annotations);
		}
		n.setType((Type) n.getType().accept(this, arg));
		final List<VariableDeclarator> vars = n.getVars();
		for (int i = 0; i < vars.size(); i++) {
			vars.set(i, (VariableDeclarator) vars.get(i).accept(this, arg));
		}
		removeNulls(vars);
		return n;
	}

	@Override public Node visit(final VariableDeclarator n, final A arg) {
		n.setId((VariableDeclaratorId) n.getId().accept(this, arg));
		if (n.getInit() != null) {
			n.setInit((Expression) n.getInit().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final VariableDeclaratorId n, final A arg) {
		return n;
	}

	@Override public Node visit(final VoidType n, final A arg) {
		return n;
	}

	@Override public Node visit(final WhileStmt n, final A arg) {
		n.setCondition((Expression) n.getCondition().accept(this, arg));
		n.setBody((Statement) n.getBody().accept(this, arg));
		return n;
	}

	@Override public Node visit(final WildcardType n, final A arg) {
		if (n.getExtends() != null) {
			n.setExtends((ReferenceType) n.getExtends().accept(this, arg));
		}
		if (n.getSuper() != null) {
			n.setSuper((ReferenceType) n.getSuper().accept(this, arg));
		}
		return n;
	}

	@Override public Node visit(final BlockComment n, final A arg) {
		return n;
	}

	@Override public Node visit(final LineComment n, final A arg) {
		return n;
	}

}
