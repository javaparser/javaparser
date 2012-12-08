/*
 * Created on 30/06/2008
 */
package japa.parser.ast.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import japa.parser.ast.BlockComment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
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
import japa.parser.ast.visitor.VoidVisitorAdapter;

import org.junit.Test;

/**
 * @author Julio Vilmar Gesser
 */
public class TestNodePositions {

	@Test public void testNodePositions() throws Exception {
		String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
		final CompilationUnit cu = Helper.parserString(source);

		cu.accept(new TestVisitor(source), null);
	}

	void doTest(final String source, final Node node) {
		final String parsed = node.toString();

		assertTrue(node.getClass().getName() + ": " + parsed, node.getBeginLine() >= 0);
		assertTrue(node.getClass().getName() + ": " + parsed, node.getBeginColumn() >= 0);
		assertTrue(node.getClass().getName() + ": " + parsed, node.getEndLine() >= 0);
		assertTrue(node.getClass().getName() + ": " + parsed, node.getEndColumn() >= 0);

		if (node.getBeginLine() == node.getEndLine()) {
			assertTrue(node.getClass().getName() + ": " + parsed, node.getBeginColumn() <= node.getEndColumn());
		} else {
			assertTrue(node.getClass().getName() + ": " + parsed, node.getBeginLine() <= node.getEndLine());
		}

		final String substr = substring(source, node.getBeginLine(), node.getBeginColumn(), node.getEndLine(),
				node.getEndColumn());
		assertEquals(node.getClass().getName(), trimLines(substr), trimLines(parsed));
	}

	private String trimLines(final String str) {
		final String[] split = str.split("\n");
		final StringBuilder ret = new StringBuilder();
		for (int i = 0; i < split.length; i++) {
			ret.append(split[i].trim());
			if (i < split.length - 1) {
				ret.append("\n");
			}
		}

		return ret.toString();
	}

	private String substring(final String source, int beginLine, final int beginColumn, int endLine, final int endColumn) {
		int pos = 0;
		while (beginLine > 1) {
			if (source.charAt(pos) == '\n') {
				beginLine--;
				endLine--;
			}
			pos++;
		}
		final int start = pos + beginColumn - 1;

		while (endLine > 1) {
			if (source.charAt(pos) == '\n') {
				endLine--;
			}
			pos++;
		}
		final int end = pos + endColumn;

		return source.substring(start, end);
	}

	class TestVisitor extends VoidVisitorAdapter<Object> {

		private final String source;

		public TestVisitor(final String source) {
			this.source = source;
		}

		@Override public void visit(final AnnotationDeclaration n, final Object arg) {
			doTest(source, n);
			doTest(source, n.getNameExpr());
			super.visit(n, arg);
		}

		@Override public void visit(final AnnotationMemberDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ArrayAccessExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ArrayCreationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ArrayInitializerExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final AssertStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final AssignExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final BinaryExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final BlockComment n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final BlockStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final BooleanLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final BreakStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final CastExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final CatchClause n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final CharLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ClassExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ClassOrInterfaceDeclaration n, final Object arg) {
			doTest(source, n);
			doTest(source, n.getNameExpr());
			super.visit(n, arg);
		}

		@Override public void visit(final ClassOrInterfaceType n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final CompilationUnit n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ConditionalExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ConstructorDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ContinueStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final DoStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final DoubleLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EmptyMemberDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EmptyStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EmptyTypeDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EnclosedExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EnumConstantDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final EnumDeclaration n, final Object arg) {
			doTest(source, n);
			doTest(source, n.getNameExpr());
			super.visit(n, arg);
		}

		@Override public void visit(final ExplicitConstructorInvocationStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ExpressionStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final FieldAccessExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final FieldDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ForeachStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ForStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final IfStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ImportDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final InitializerDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final InstanceOfExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final IntegerLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final IntegerLiteralMinValueExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final JavadocComment n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final LabeledStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final LineComment n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final LongLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final LongLiteralMinValueExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final MarkerAnnotationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final MemberValuePair n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final MethodCallExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final MethodDeclaration n, final Object arg) {
			doTest(source, n);
			doTest(source, n.getNameExpr());
			super.visit(n, arg);
		}

		@Override public void visit(final NameExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final NormalAnnotationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final NullLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ObjectCreationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final PackageDeclaration n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final Parameter n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final PrimitiveType n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final QualifiedNameExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ReferenceType n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ReturnStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final SingleMemberAnnotationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final StringLiteralExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final SuperExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final SwitchEntryStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final SwitchStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final SynchronizedStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ThisExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final ThrowStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final TryStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final TypeDeclarationStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final TypeParameter n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final UnaryExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final VariableDeclarationExpr n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final VariableDeclarator n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final VariableDeclaratorId n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final VoidType n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final WhileStmt n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

		@Override public void visit(final WildcardType n, final Object arg) {
			doTest(source, n);
			super.visit(n, arg);
		}

	}

}
