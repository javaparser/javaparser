package com.github.jmlparser.jml2java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
public class Jml2JavaTranslator {
    private final AtomicInteger counter = new AtomicInteger();

    public Expression accept(Expression e, BlockStmt arg) {
        if (Jml2JavaFacade.containsJmlExpression(e)) {
            return e.accept(new Jml2JavaVisitor(), arg);
        }
        return e; // createAssignmentAndAdd(e, arg);
    }

    private Expression createAssignmentAndAdd(Expression e, BlockStmt arg) {
        arg.addAndGetStatement(createAssignmentFor(e));
        return new NameExpr(getTargetForAssignment());
    }

    private Statement createAssignmentFor(Expression e) {
        var decl = new VariableDeclarationExpr(
                new VariableDeclarator(new VarType(),
                        newTargetForAssignment(), e));
        decl.addModifier(Modifier.DefaultKeyword.FINAL);
        return new ExpressionStmt(decl);
    }

    private SimpleName getTargetForAssignment() {
        return new SimpleName("_gen_" + counter.get());
    }

    private SimpleName newTargetForAssignment() {
        counter.getAndIncrement();
        return getTargetForAssignment();
    }

    private final class Jml2JavaVisitor extends GenericVisitorAdapter<Expression, BlockStmt> {
        @Override
        public Expression visit(JmlQuantifiedExpr n, BlockStmt arg) {
            if (n.getBinder() == JmlQuantifiedExpr.JmlDefaultBinder.FORALL)
                return visitForall(n, arg);
            if (n.getBinder() == JmlQuantifiedExpr.JmlDefaultBinder.EXISTS)
                return visitExists(n, arg);

            throw new IllegalArgumentException("Unsupport quantifier " + n.getBinder());
        }

        private Expression visitForall(JmlQuantifiedExpr n, BlockStmt arg) {
            final var EXISTS_TEMPLATE = """
                    boolean rvalue = true;
                    for (int i = low; i < high; i++) {
                        if(!(pred)) {
                            rvalue = false;
                            break;
                        }
                    }
                    """;

            return null;
        }

        private Expression visitExists(JmlQuantifiedExpr n, BlockStmt arg) {
            final var EXISTS_TEMPLATE = """
                    boolean rvalue = false;
                    for (int i = low; i < high; i++) {
                        if(pred) {
                            rvalue = true;
                            break;
                        }
                    }
                    """;

            return createAssignmentAndAdd(n, arg);
        }

        @Override
        public Expression visit(BinaryExpr n, BlockStmt arg) {
            var left = accept(n.getLeft(), arg);
            var right = accept(n.getRight(), arg);
            switch (n.getOperator()) {
                case IMPLICATION:
                    return new BinaryExpr(
                            new UnaryExpr(new EnclosedExpr(left), UnaryExpr.Operator.LOGICAL_COMPLEMENT),
                            right,
                            BinaryExpr.Operator.OR);
                case RIMPLICATION:
                    return
                            new BinaryExpr(
                                    left,
                                    new UnaryExpr(new EnclosedExpr(right), UnaryExpr.Operator.LOGICAL_COMPLEMENT),
                                    BinaryExpr.Operator.OR);
                case EQUIVALENCE:
                    return new BinaryExpr(left, right, BinaryExpr.Operator.EQUALS);
                case SUBTYPE:
                case SUB_LOCK:
                case SUB_LOCKE:
                    throw new IllegalArgumentException("Unsupported operators.");
                default:
                    return createAssignmentAndAdd(
                            new BinaryExpr(left, right, n.getOperator()),
                            arg);
            }
        }

        @Override
        public Expression visit(ArrayAccessExpr n, BlockStmt arg) {
            return super.visit(n, arg);
        }

        @Override
        public Expression visit(ArrayCreationExpr n, BlockStmt arg) {
            return super.visit(n, arg);
        }

        @Override
        public Expression visit(ArrayInitializerExpr n, BlockStmt arg) {
            return super.visit(n, arg);
        }

        @Override
        public Expression visit(AssignExpr n, BlockStmt arg) {
            return super.visit(n, arg);
        }


    }
}
