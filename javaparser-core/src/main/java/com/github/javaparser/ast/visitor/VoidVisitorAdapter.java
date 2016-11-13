/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 * 
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License 
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
 
package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithArrays;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.List;

import static com.github.javaparser.utils.Utils.isNullOrEmpty;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class VoidVisitorAdapter<A> implements VoidVisitor<A> {

	@Override public void visit(final AnnotationDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getNameExpr().accept(this, arg);
		if (n.getMembersList() != null) {
            for (final BodyDeclaration<?> member : n.getMembersList()) {
				member.accept(this, arg);
			}
		}
	}

	@Override public void visit(final AnnotationMemberDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getType().accept(this, arg);
		if (n.getDefaultValue() != null) {
			n.getDefaultValue().accept(this, arg);
		}
	}

	@Override public void visit(final ArrayAccessExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getName().accept(this, arg);
		n.getIndex().accept(this, arg);
	}

	@Override public void visit(final ArrayCreationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		visitArraysAnnotations(n, arg);
		n.getType().accept(this, arg);
		if (!isNullOrEmpty(n.getDimensionsList())) {
			for (final Expression dim : n.getDimensionsList()) {
				dim.accept(this, arg);
			}
		}
		if (n.getInitializer() != null) {
			n.getInitializer().accept(this, arg);
		}
	}

	@Override public void visit(final ArrayInitializerExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getValuesList() != null) {
			for (final Expression expr : n.getValuesList()) {
				expr.accept(this, arg);
			}
		}
	}

	@Override public void visit(final AssertStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getCheck().accept(this, arg);
		if (n.getMsg() != null) {
			n.getMsg().accept(this, arg);
		}
	}

	@Override public void visit(final AssignExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getTarget().accept(this, arg);
		n.getValue().accept(this, arg);
	}

	@Override public void visit(final BinaryExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getLeft().accept(this, arg);
		n.getRight().accept(this, arg);
	}

	@Override public void visit(final BlockComment n, final A arg) {
	}

	@Override public void visit(final BlockStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getStmtsList() != null) {
			for (final Statement s : n.getStmtsList()) {
				s.accept(this, arg);
			}
		}
	}

	@Override public void visit(final BooleanLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final BreakStmt n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final CastExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getType().accept(this, arg);
		n.getExpr().accept(this, arg);
	}

	@Override public void visit(final CatchClause n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getParam().accept(this, arg);
		n.getCatchBlock().accept(this, arg);
	}

	@Override public void visit(final CharLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final ClassExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getType().accept(this, arg);
	}

	@Override public void visit(final ClassOrInterfaceDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getNameExpr().accept(this, arg);
		for (final TypeParameter t : n.getTypeParameterList()) {
			t.accept(this, arg);
		}
		for (final ClassOrInterfaceType c : n.getExtendsList()) {
			c.accept(this, arg);
		}
		for (final ClassOrInterfaceType c : n.getImplementsList()) {
			c.accept(this, arg);
		}
        for (final BodyDeclaration<?> member : n.getMembersList()) {
			member.accept(this, arg);
		}
	}

	@Override public void visit(final ClassOrInterfaceType n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		if (n.getScope() != null) {
			n.getScope().accept(this, arg);
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				t.accept(this, arg);
			}
		}
	}

	@Override public void visit(final CompilationUnit n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getPackage() != null) {
			n.getPackage().accept(this, arg);
		}
		if (n.getImportsList() != null) {
			for (final ImportDeclaration i : n.getImportsList()) {
				i.accept(this, arg);
			}
		}
		if (n.getTypesList() != null) {
            for (final TypeDeclaration<?> typeDeclaration : n.getTypesList()) {
				typeDeclaration.accept(this, arg);
			}
		}
	}

	@Override public void visit(final ConditionalExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getCondition().accept(this, arg);
		n.getThenExpr().accept(this, arg);
		n.getElseExpr().accept(this, arg);
	}

	@Override public void visit(final ConstructorDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		if (n.getTypeParameterList() != null) {
			for (final TypeParameter t : n.getTypeParameterList()) {
				t.accept(this, arg);
			}
		}
		n.getNameExpr().accept(this, arg);
		if (n.getParametersList() != null) {
			for (final Parameter p : n.getParametersList()) {
				p.accept(this, arg);
			}
		}
		if (n.getThrowsList() != null) {
			for (final ReferenceType name : n.getThrowsList()) {
				name.accept(this, arg);
			}
		}
		n.getBody().accept(this, arg);
	}

	@Override public void visit(final ContinueStmt n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final DoStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getBody().accept(this, arg);
		n.getCondition().accept(this, arg);
	}

	@Override public void visit(final DoubleLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final EmptyMemberDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final EmptyStmt n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final EmptyTypeDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getNameExpr().accept(this, arg);
	}

	@Override public void visit(final EnclosedExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getInner().accept(this, arg);
	}

	@Override public void visit(final EnumConstantDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				e.accept(this, arg);
			}
		}
		if (n.getClassBodyList() != null) {
            for (final BodyDeclaration<?> member : n.getClassBodyList()) {
				member.accept(this, arg);
			}
		}
	}

	@Override public void visit(final EnumDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getNameExpr().accept(this, arg);
		if (n.getImplementsList() != null) {
			for (final ClassOrInterfaceType c : n.getImplementsList()) {
				c.accept(this, arg);
			}
		}
		if (n.getEntriesList() != null) {
			for (final EnumConstantDeclaration e : n.getEntriesList()) {
				e.accept(this, arg);
			}
		}
		if (n.getMembersList() != null) {
            for (final BodyDeclaration<?> member : n.getMembersList()) {
				member.accept(this, arg);
			}
		}
	}

	@Override public void visit(final ExplicitConstructorInvocationStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (!n.isThis() && n.getExpr() != null) {
			n.getExpr().accept(this, arg);
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				t.accept(this, arg);
			}
		}
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				e.accept(this, arg);
			}
		}
	}

	@Override public void visit(final ExpressionStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getExpr().accept(this, arg);
	}

	@Override public void visit(final FieldAccessExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getScope().accept(this, arg);
		n.getFieldExpr().accept(this, arg);
	}

	@Override public void visit(final FieldDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getType().accept(this, arg);
		for (final VariableDeclarator var : n.getVariablesList()) {
			var.accept(this, arg);
		}
	}

	@Override public void visit(final ForeachStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getVar().accept(this, arg);
		n.getIterable().accept(this, arg);
		n.getBody().accept(this, arg);
	}

	@Override public void visit(final ForStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getInitList() != null) {
			for (final Expression e : n.getInitList()) {
				e.accept(this, arg);
			}
		}
		if (n.getCompare() != null) {
			n.getCompare().accept(this, arg);
		}
		if (n.getUpdateList() != null) {
			for (final Expression e : n.getUpdateList()) {
				e.accept(this, arg);
			}
		}
		n.getBody().accept(this, arg);
	}

	@Override public void visit(final IfStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getCondition().accept(this, arg);
		n.getThenStmt().accept(this, arg);
		if (n.getElseStmt() != null) {
			n.getElseStmt().accept(this, arg);
		}
	}

	@Override public void visit(final ImportDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getName().accept(this, arg);
	}

	@Override public void visit(final InitializerDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getBlock().accept(this, arg);
	}

	@Override public void visit(final InstanceOfExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getExpr().accept(this, arg);
		n.getType().accept(this, arg);
	}

	@Override public void visit(final IntegerLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final IntegerLiteralMinValueExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final JavadocComment n, final A arg) {
	}

	@Override public void visit(final LabeledStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getStmt().accept(this, arg);
	}

	@Override public void visit(final LineComment n, final A arg) {
	}

	@Override public void visit(final LongLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final LongLiteralMinValueExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final MarkerAnnotationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getName().accept(this, arg);
	}

	@Override public void visit(final MemberValuePair n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getValue().accept(this, arg);
	}

	@Override public void visit(final MethodCallExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getScope() != null) {
			n.getScope().accept(this, arg);
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				t.accept(this, arg);
			}
		}
		n.getNameExpr().accept(this, arg);
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				e.accept(this, arg);
			}
		}
	}

	@Override public void visit(final MethodDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		if (n.getTypeParametersList() != null) {
			for (final TypeParameter t : n.getTypeParametersList()) {
				t.accept(this, arg);
			}
		}
		n.getType().accept(this, arg);
		n.getNameExpr().accept(this, arg);
		if (n.getParametersList() != null) {
			for (final Parameter p : n.getParametersList()) {
				p.accept(this, arg);
			}
		}
		if (n.getThrowsList() != null) {
			for (final ReferenceType name : n.getThrowsList()) {
				name.accept(this, arg);
			}
		}
		if (n.getBody() != null) {
			n.getBody().accept(this, arg);
		}
	}

	@Override public void visit(final NameExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final NormalAnnotationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getName().accept(this, arg);
		if (n.getPairsList() != null) {
			for (final MemberValuePair m : n.getPairsList()) {
				m.accept(this, arg);
			}
		}
	}

	@Override public void visit(final NullLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final ObjectCreationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getScope() != null) {
			n.getScope().accept(this, arg);
		}
		if (n.getTypeArgsList() != null) {
			for (final Type t : n.getTypeArgsList()) {
				t.accept(this, arg);
			}
		}
		n.getType().accept(this, arg);
		if (n.getArgsList() != null) {
			for (final Expression e : n.getArgsList()) {
				e.accept(this, arg);
			}
		}
		if (n.getAnonymousClassBodyList() != null) {
            for (final BodyDeclaration<?> member : n.getAnonymousClassBodyList()) {
				member.accept(this, arg);
			}
		}
	}

	@Override public void visit(final PackageDeclaration n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getName().accept(this, arg);
	}

	@Override public void visit(final Parameter n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getType().accept(this, arg);
		n.getId().accept(this, arg);
	}
	
	@Override public void visit(final PrimitiveType n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
	}

	@Override public void visit(final QualifiedNameExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getQualifier().accept(this, arg);
	}

	@Override public void visit(final ReferenceType n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		visitArraysAnnotations(n, arg);
		n.getType().accept(this, arg);
	}

    @Override public void visit(final IntersectionType n, final A arg) {
        visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		for (ReferenceType element : n.getElementsList()) {
            element.accept(this, arg);
        }
    }

    @Override public void visit(final UnionType n, final A arg) {
        visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		for (ReferenceType element : n.getElementsList()) {
            element.accept(this, arg);
        }
    }

	@Override public void visit(final ReturnStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getExpr() != null) {
			n.getExpr().accept(this, arg);
		}
	}

	@Override public void visit(final SingleMemberAnnotationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getName().accept(this, arg);
		n.getMemberValue().accept(this, arg);
	}

	@Override public void visit(final StringLiteralExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final SuperExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getClassExpr() != null) {
			n.getClassExpr().accept(this, arg);
		}
	}

	@Override public void visit(final SwitchEntryStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getLabel() != null) {
			n.getLabel().accept(this, arg);
		}
		if (n.getStmtsList() != null) {
			for (final Statement s : n.getStmtsList()) {
				s.accept(this, arg);
			}
		}
	}

	@Override public void visit(final SwitchStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getSelector().accept(this, arg);
		if (n.getEntriesList() != null) {
			for (final SwitchEntryStmt e : n.getEntriesList()) {
				e.accept(this, arg);
			}
		}
	}

	@Override public void visit(final SynchronizedStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getExpr().accept(this, arg);
		n.getBlock().accept(this, arg);
	}

	@Override public void visit(final ThisExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getClassExpr() != null) {
			n.getClassExpr().accept(this, arg);
		}
	}

	@Override public void visit(final ThrowStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getExpr().accept(this, arg);
	}

	@Override public void visit(final TryStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getResourcesList() != null) {
			for (final VariableDeclarationExpr v : n.getResourcesList()) {
				v.accept(this, arg);
			}
		}
		n.getTryBlock().accept(this, arg);
		if (n.getCatchsList() != null) {
			for (final CatchClause c : n.getCatchsList()) {
				c.accept(this, arg);
			}
		}
		if (n.getFinallyBlock() != null) {
			n.getFinallyBlock().accept(this, arg);
		}
	}

	@Override public void visit(final TypeDeclarationStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getTypeDeclaration().accept(this, arg);
	}

	@Override public void visit(final TypeParameter n, final A arg) {
		visitComment(n.getComment(), arg);
		if (n.getTypeBoundList() != null) {
			for (final ClassOrInterfaceType c : n.getTypeBoundList()) {
				c.accept(this, arg);
			}
		}
	}

	@Override public void visit(final UnaryExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getExpr().accept(this, arg);
	}

	@Override public void visit(final UnknownType n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final VariableDeclarationExpr n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		n.getType().accept(this, arg);
		for (final VariableDeclarator v : n.getVarsList()) {
			v.accept(this, arg);
		}
	}

	@Override public void visit(final VariableDeclarator n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getId().accept(this, arg);
		if (n.getInit() != null) {
			n.getInit().accept(this, arg);
		}
	}

	@Override public void visit(final VariableDeclaratorId n, final A arg) {
		visitComment(n.getComment(), arg);
	}

	@Override public void visit(final VoidType n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);

	}

	@Override public void visit(final WhileStmt n, final A arg) {
		visitComment(n.getComment(), arg);
		n.getCondition().accept(this, arg);
		n.getBody().accept(this, arg);
	}

	@Override public void visit(final WildcardType n, final A arg) {
		visitComment(n.getComment(), arg);
		visitAnnotations(n, arg);
		if (n.getExtends() != null) {
			n.getExtends().accept(this, arg);
		}
		if (n.getSuper() != null) {
			n.getSuper().accept(this, arg);
		}
	}

    @Override
    public void visit(LambdaExpr n, final A arg) {
		visitComment(n.getComment(), arg);
        if (n.getParametersList() != null) {
            for (final Parameter a : n.getParametersList()) {
                a.accept(this, arg);
            }
        }
        if (n.getBody() != null) {
            n.getBody().accept(this, arg);
        }
    }

    @Override
    public void visit(MethodReferenceExpr n, final A arg) {
		visitComment(n.getComment(), arg);
	    if (n.getTypeArguments().getTypeArgumentsList() != null) {
		    for (final Type t : n.getTypeArguments().getTypeArgumentsList()) {
			    t.accept(this, arg);
		    }
	    }
        if (n.getScope() != null) {
            n.getScope().accept(this, arg);
        }
    }

    @Override
    public void visit(TypeExpr n, final A arg) {
		visitComment(n.getComment(), arg);
        if (n.getType() != null) {
            n.getType().accept(this, arg);
        }
    }

    private void visitComment(final Comment n, final A arg) {
		if (n != null) {
			n.accept(this, arg);
		}
	}

	private void visitAnnotations(NodeWithAnnotations<?> n, A arg) {
		for (AnnotationExpr annotation : n.getAnnotationsList()) {
			annotation.accept(this, arg);
		}
	}

	private void visitArraysAnnotations(NodeWithArrays<?> n, A arg) {
		for (List<AnnotationExpr> aux : n.getArraysAnnotationsList()) {
			if (aux != null) {
				for (AnnotationExpr annotation : aux) {
					annotation.accept(this, arg);
				}
			}
		}
	}
}
