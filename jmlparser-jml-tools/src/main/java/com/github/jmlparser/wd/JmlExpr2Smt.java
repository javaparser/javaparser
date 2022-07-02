package com.github.jmlparser.wd;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlDefaultBinder;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.jmlparser.utils.JMLUtils;
import org.sosy_lab.java_smt.api.*;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public class JmlExpr2Smt extends GenericVisitorAdapter<Formula, Object> {
    private final SolverContext context;
    private final Translator translator;
    private final BooleanFormulaManager boolmgr;
    //private final StringFormulaManager smgr;
    private final QuantifiedFormulaManager qmgr;

    public JmlExpr2Smt(SolverContext context) {
        this.context = context;
        this.boolmgr = context.getFormulaManager().getBooleanFormulaManager();
        //this.smgr = context.getFormulaManager().getStringFormulaManager();
        qmgr = context.getFormulaManager().getQuantifiedFormulaManager();
        translator = new BitVectorTranslator(context);
    }

    @Override
    public Formula visit(ArrayAccessExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(ArrayCreationExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(ArrayInitializerExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(AssignExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(BinaryExpr n, Object arg) {
        Formula left = n.getLeft().accept(this, arg);
        Formula right = n.getRight().accept(this, arg);
        return translator.binary(n.getOperator(), left, right);
    }

    @Override
    public Formula visit(BooleanLiteralExpr n, Object arg) {
        return boolmgr.makeBoolean(n.getValue());
    }

    @Override
    public Formula visit(CastExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(CharLiteralExpr n, Object arg) {
        return translator.makeChar(n);
    }

    @Override
    public Formula visit(ClassExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(ConditionalExpr n, Object arg) {
        return translator.conditional(n.getCondition().accept(this, arg),
                n.getThenExpr().accept(this, arg),
                n.getElseExpr().accept(this, arg));
    }

    @Override
    public Formula visit(DoubleLiteralExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(FieldAccessExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(InstanceOfExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(IntegerLiteralExpr n, Object arg) {
        return translator.makeInt(n);
    }

    @Override
    public Formula visit(LongLiteralExpr n, Object arg) {
        return translator.makeLong(n);
    }

    @Override
    public Formula visit(MethodCallExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(ObjectCreationExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(StringLiteralExpr n, Object arg) {
        return null;
        // return smgr.makeString(n.getValue());
    }

    @Override
    public Formula visit(UnaryExpr n, Object arg) {
        return translator.unary(n.getOperator(), n.getExpression().accept(this, arg));
    }

    @Override
    public Formula visit(LambdaExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(TypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(SwitchExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(TextBlockLiteralExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(PatternExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(JmlQuantifiedExpr n, Object arg) {
        switch ((JmlDefaultBinder) n.getBinder()) {
            case FORALL:
                Expression e = new BinaryExpr(n.getExpressions().get(0), n.getExpressions().get(1), BinaryExpr.Operator.IMPLICATION);
                return qmgr.forall(translator.getVariable(n.getVariables()), (BooleanFormula) e.accept(this, arg));
            case EXISTS:
                Expression e1 = new BinaryExpr(n.getExpressions().get(0), n.getExpressions().get(1), BinaryExpr.Operator.AND);
                return qmgr.forall(translator.getVariable(n.getVariables()), (BooleanFormula) e1.accept(this, arg));
            case BSUM:
            case MIN:
            case MAX:
            case PRODUCT:
                return translator.makeIntVar();
            default:
                return null;
        }
    }

    @Override
    public Formula visit(JmlLabelExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public Formula visit(JmlLetExpr n, Object arg) {
        return null;
    }

    @Override
    public Formula visit(JmlMultiCompareExpr n, Object arg) {
        return JMLUtils.unroll(n).accept(this, arg);
    }

    @Override
    public Formula visit(JmlBinaryInfixExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public Formula visit(JmlTypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    public Translator getTranslator() {
        return translator;
    }
}
