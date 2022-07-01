package com.github.jmlparser.wd;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.sosy_lab.java_smt.api.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
public class WDVisitor extends VoidVisitorAdapter<Object> {
    private final SolverContext context;
    private final IntegerFormulaManager imgr;

    public WDVisitor(SolverContext context) {
        this.context = context;
        this.imgr = context.getFormulaManager().getIntegerFormulaManager();
    }

    @Override
    public void visit(JmlExpressionStmt n, Object arg) {
        n.getExpression().accept(this, arg);
    }

}

class WDVisitorExpr extends GenericVisitorAdapter<BooleanFormula, Object> {
    private final SolverContext context;
    private final BitvectorFormulaManager bitmgr;
    private final IntegerFormulaManager imgr;
    private final BooleanFormulaManager bmgr;
    private final QuantifiedFormulaManager qmgr;

    private GenericVisitor<? extends NumeralFormula.IntegerFormula, ? super Object> smtFormula;

    WDVisitorExpr(SolverContext context) {
        this.context = context;
        this.imgr = context.getFormulaManager().getIntegerFormulaManager();
        this.bmgr = context.getFormulaManager().getBooleanFormulaManager();
        this.bitmgr = context.getFormulaManager().getBitvectorFormulaManager();
        this.qmgr = context.getFormulaManager().getQuantifiedFormulaManager();
    }

    @Override
    public BooleanFormula visit(NameExpr n, Object arg) {
        String name = n.getNameAsString();
        switch (name) {
            case "\\result":
            case "\\exception":
                return bmgr.makeTrue();
            default:
                return bmgr.makeTrue();
        }
    }

    @Override
    public BooleanFormula visit(ArrayAccessExpr n, Object arg) {
        return bmgr.and(
                n.getName().accept(this, arg),
                n.getIndex().accept(this, arg));
    }

    @Override
    public BooleanFormula visit(ArrayCreationExpr n, Object arg) {
        //TODO
        return n.getInitializer().get().accept(this, arg);
    }

    @Override
    public BooleanFormula visit(ArrayInitializerExpr n, Object arg) {
        List<BooleanFormula> seq = n.getValues().stream().map(it -> it.accept(this, arg)).collect(Collectors.toList());
        return bmgr.and(seq);
    }

    @Override
    public BooleanFormula visit(AssignExpr n, Object arg) {
        return bmgr.makeFalse();
    }

    @Override
    public BooleanFormula visit(BinaryExpr n, Object arg) {
        switch (n.getOperator()) {
            case IMPLICATION:
                BinaryExpr be = new BinaryExpr(
                        new UnaryExpr(n.getLeft(), UnaryExpr.Operator.LOGICAL_COMPLEMENT),
                        n.getRight(), BinaryExpr.Operator.OR);
                return be.accept(this, arg);
            case DIVIDE:
            case REMAINDER:
                NumeralFormula.IntegerFormula value = n.accept(smtFormula, arg);
                return bmgr.and(
                        n.getRight().accept(this, arg),
                        n.getLeft().accept(this, arg),
                        bmgr.not(imgr.equal(value, imgr.makeNumber(0))));
            default:
                return bmgr.and(
                        n.getRight().accept(this, arg),
                        n.getLeft().accept(this, arg));
        }
    }

    @Override
    public BooleanFormula visit(BooleanLiteralExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(CastExpr n, Object arg) {
        //TODO Type-check?
        return n.getExpression().accept(this, arg);
    }

    @Override
    public BooleanFormula visit(CharLiteralExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(ClassExpr n, Object arg) {
        return bmgr.makeFalse();
    }

    @Override
    public BooleanFormula visit(DoubleLiteralExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(EnclosedExpr n, Object arg) {
        return wd(n.getInner());
    }

    @Override
    public BooleanFormula visit(FieldAccessExpr n, Object arg) {
        return wd(n.getScope());
    }

    @Override
    public BooleanFormula visit(InstanceOfExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public BooleanFormula visit(IntegerLiteralExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(SingleMemberAnnotationExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(StringLiteralExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(SuperExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(ThisExpr n, Object arg) {
        return bmgr.makeTrue();
    }

    @Override
    public BooleanFormula visit(UnaryExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public BooleanFormula visit(VariableDeclarationExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(LambdaExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(MethodReferenceExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(TypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(SwitchExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(TextBlockLiteralExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(PatternExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlQuantifiedExpr n, Object arg) {
        /*The quantified-expression is well-defined iff the two sub-expressions are well-defined. For a quantifier Q*/
        List<BooleanFormula> seq = n.getExpressions().stream()
                .map(it -> it.accept(this, arg))
                .collect(Collectors.toList());

        Expression r = n.getExpressions().get(0);
        Expression v = n.getExpressions().get(0);

        List<Formula> args = new ArrayList<>();

        if (JmlQuantifiedExpr.JmlDefaultBinder.CHOOSE.equals(n.getBinder())) {
            return bmgr.and(
                    qmgr.forall(args, wd(r)),
                    qmgr.forall(args, bmgr.implication((BooleanFormula) valueOf(r), wd(v))),
                    qmgr.exists(args, bmgr.and(
                            (BooleanFormula) valueOf(r),
                            (BooleanFormula) valueOf(v))));
        }
        return bmgr.and(
                qmgr.forall(args, wd(r)),
                qmgr.forall(args, bmgr.implication((BooleanFormula) valueOf(r), wd(v))));
    }

    private Formula valueOf(Expression e) {
        return e.accept(smtFormula, null);
    }

    private BooleanFormula wd(Expression e) {
        return e.accept(this, null);
    }

    @Override
    public BooleanFormula visit(JmlExpressionStmt n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlLabelExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlLetExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlClassExprDeclaration n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlTypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(JmlMultiExprClause n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public BooleanFormula visit(MethodCallExpr n, Object arg) {
        String name = n.getNameAsString();
        switch (name) {
            case "\\old":
            case "\\pre":
            case "\\past":
                /* Well-definedness: The expression is well-defined if the first argument is well-defined
                   and any label argument names either a built-in label (§11.611.6) or an in-scope Java or
                   JML ghost label (S11.511.5).*/
                return n.getArguments().get(0).accept(this, arg);
            case "\\fresh":
                /* Well-definedness: The argument must be well-defined and non-null. The second argument,
                   if present, must be the identifier corresponding to an in-scope label or a built-in label. */
                return n.getArguments().get(0).accept(this, arg);
            //TODO valueOf(n.getArguments().get(0)) != null
        }

        List<BooleanFormula> seq = n.getArguments().stream()
                .map(it -> it.accept(this, arg))
                .collect(Collectors.toList());
        return bmgr.and(seq);
    }
}
