package com.github.jmlparser.jml2java;

import com.beust.ah.A;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.JmlLetExpr;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.jmlparser.utils.JMLUtils;
import com.github.jmlparser.utils.Pattern;

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

    public Expression findPredicate(JmlQuantifiedExpr n) {
        return n.getExpressions().get(n.getExpressions().size() - 1);
    }

    public static Expression findBound(JmlQuantifiedExpr n) {
        if (n.getExpressions().size() == 2)
            return n.getExpressions().get(0);
        else if (n.getExpressions().size() == 1)
            if (n.getExpressions().get(0) instanceof BinaryExpr be)
                return be.getLeft();
        throw new IllegalArgumentException("Could not determine bound.");

    }

    public static Expression findLowerBound(JmlQuantifiedExpr n, String variable) {
        if (n.getExpressions().size() == 3) return n.getExpressions().get(0);

        var e = findBound(n);

        if (e instanceof JmlMultiCompareExpr mc) {
            if (mc.getExpressions().size() == 3 &&
                    mc.getExpressions().get(1) instanceof NameExpr v &&
                    v.getNameAsString().equals(variable)) {
                if (mc.getOperators().get(0) == BinaryExpr.Operator.LESS_EQUALS)
                    return mc.getExpressions().get(0);
                if (mc.getOperators().get(0) == BinaryExpr.Operator.LESS)
                    return new BinaryExpr(mc.getExpressions().get(0), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
                throw new IllegalStateException();
            }
        }

        Expression ph = new NameExpr("_");
        {
            var be = new BinaryExpr(new NameExpr(variable), ph, BinaryExpr.Operator.GREATER_EQUALS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return (Expression) result.get("min");
        }

        {
            var be = new BinaryExpr(new NameExpr(variable), ph, BinaryExpr.Operator.GREATER);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return new BinaryExpr((Expression) result.get("min"), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
        }

        {
            var be = new BinaryExpr(ph, new NameExpr(variable), BinaryExpr.Operator.LESS_EQUALS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return (Expression) result.get("min");
        }

        {
            var be = new BinaryExpr(ph, new NameExpr(variable), BinaryExpr.Operator.LESS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return new BinaryExpr((Expression) result.get("min"), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
        }

        return null;
    }

    public Expression findUpperBound(JmlQuantifiedExpr n, String variable) {
        if (n.getExpressions().size() == 3) return n.getExpressions().get(1);

        var e = findBound(n);

        if (e instanceof JmlMultiCompareExpr mc) {
            if (mc.getExpressions().size() == 3 &&
                    mc.getExpressions().get(1) instanceof NameExpr v &&
                    v.getNameAsString().equals(variable)) {
                if (mc.getOperators().get(0) == BinaryExpr.Operator.LESS_EQUALS)
                    return mc.getExpressions().get(0);
                if (mc.getOperators().get(0) == BinaryExpr.Operator.LESS)
                    return new BinaryExpr(mc.getExpressions().get(0), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
                throw new IllegalStateException();
            }
        }

        Expression ph = new NameExpr("_");
        {
            var be = new BinaryExpr(new NameExpr(variable), ph, BinaryExpr.Operator.GREATER_EQUALS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return (Expression) result.get("min");
        }

        {
            var be = new BinaryExpr(new NameExpr(variable), ph, BinaryExpr.Operator.GREATER);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return new BinaryExpr((Expression) result.get("min"), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
        }

        {
            var be = new BinaryExpr(ph, new NameExpr(variable), BinaryExpr.Operator.LESS_EQUALS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return (Expression) result.get("min");
        }

        {
            var be = new BinaryExpr(ph, new NameExpr(variable), BinaryExpr.Operator.LESS);
            var pattern = new Pattern<>(be);
            pattern.addPlaceholder(ph, "min");
            var result = pattern.find(n);
            if (result != null)
                return new BinaryExpr((Expression) result.get("min"), new IntegerLiteralExpr(1), BinaryExpr.Operator.PLUS);
        }

        return null;
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
            assert n.getVariables().size() == 1;
            var rvalue = newSymbol("result_");
            var highVar = newSymbol("high_");
            var predVar = newSymbol("pred_");

            arg.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(
                            new VariableDeclarator(
                                    new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
                                    rvalue, new BooleanLiteralExpr(true)))));

            var variable = n.getVariables().get(0);
            var lowCode = Jml2JavaFacade.translate(findLowerBound(n, variable.getNameAsString()));
            arg.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(
                            new VariableDeclarator(
                                    variable.getType().clone(), variable.getNameAsString()))));
            lowCode.a.addAndGetStatement(
                    new ExpressionStmt(
                            new AssignExpr(
                                    new NameExpr(variable.getNameAsString()), lowCode.b,
                                    AssignExpr.Operator.ASSIGN)));
            arg.addAndGetStatement(lowCode.a);

            var highCode = Jml2JavaFacade.translate(findUpperBound(n, variable.getNameAsString()));
            arg.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(
                            new VariableDeclarator(
                                    variable.getType().clone(), highVar))));
            highCode.a.addAndGetStatement(
                    new ExpressionStmt(
                            new AssignExpr(
                                    new NameExpr(highVar), highCode.b,
                                    AssignExpr.Operator.ASSIGN)));
            arg.addAndGetStatement(highCode.a.clone());

            var predCode = Jml2JavaFacade.translate(findPredicate(n));

            WhileStmt whileStmt = arg.addAndGetStatement(new WhileStmt());
            var lessThanExpr = new BinaryExpr(new NameExpr(variable.getNameAsString()),
                    new NameExpr(highVar), BinaryExpr.Operator.LESS);
            whileStmt.setCondition(
                    new BinaryExpr(lessThanExpr, new NameExpr(rvalue), BinaryExpr.Operator.AND));
            var body = new BlockStmt();

            body.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(
                            new VariableDeclarator(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN), predVar))));
            predCode.a.addAndGetStatement(
                    new ExpressionStmt(
                            new AssignExpr(
                                    new NameExpr(predVar), predCode.b,
                                    AssignExpr.Operator.ASSIGN)));
            body.addAndGetStatement(predCode.a);

            final var assignPred = new ExpressionStmt(new AssignExpr(new NameExpr(rvalue),
                    new BooleanLiteralExpr(true), AssignExpr.Operator.ASSIGN));
            body.addAndGetStatement(
                    new IfStmt(new NameExpr(predVar), assignPred, null));
            body.addAndGetStatement(highCode.a.clone());

            whileStmt.setBody(body);
            return new NameExpr(rvalue);
        }

        private String newSymbol(String prefix) {
            return prefix + counter.getAndIncrement();
        }

        private Expression visitExists(JmlQuantifiedExpr n, BlockStmt arg) {
            return new UnaryExpr(visitForall(n, arg), UnaryExpr.Operator.LOGICAL_COMPLEMENT);
        }


        @Override
        public Expression visit(JmlLetExpr n, BlockStmt arg) {
            var inner = new BlockStmt();
            SimpleName target = newTargetForAssignment();
            var type = n.getBody().calculateResolvedType();
            arg.addAndGetStatement(
                    new ExpressionStmt(new VariableDeclarationExpr(JMLUtils.resolvedType2Type(type),
                            target.asString())));
            inner.addAndGetStatement(new ExpressionStmt(n.getVariables()));
            var e = accept(n.getBody(), inner);
            arg.addAndGetStatement(inner);
            inner.addAndGetStatement(new AssignExpr(new NameExpr(target.asString()), e, AssignExpr.Operator.ASSIGN));
            return new NameExpr(target.asString());
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
