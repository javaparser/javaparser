package com.github.jmlparser.wd;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.expr.JmlLabelExpr;
import com.github.javaparser.ast.jml.expr.JmlLetExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.jml.expr.JmlTypeExpr;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.jmlparser.smt.ArithmeticTranslator;
import com.github.jmlparser.smt.JmlExpr2Smt;
import com.github.jmlparser.smt.SmtQuery;
import com.github.jmlparser.smt.SmtTermFactory;
import com.github.jmlparser.smt.model.SExpr;
import org.jetbrains.annotations.NotNull;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
public class WDVisitor extends VoidVisitorAdapter<Object> {
    public WDVisitor() {
    }

    @Override
    public void visit(JmlExpressionStmt n, Object arg) {
        n.getExpression().accept(this, arg);
    }
}

class WDVisitorExpr extends GenericVisitorAdapter<SExpr, Object> {
    @NotNull
    private final JmlExpr2Smt smtFormula;
    private final ArithmeticTranslator translator;

    private static final SmtTermFactory term = SmtTermFactory.INSTANCE;

    WDVisitorExpr(SmtQuery smtLog, ArithmeticTranslator translator) {
        smtFormula = new JmlExpr2Smt(smtLog, translator);
        this.translator = translator;
    }

    @Override
    public SExpr visit(NameExpr n, Object arg) {
        String name = n.getNameAsString();
        switch (name) {
            case "\\result":
            case "\\exception":
                return term.makeTrue();
            default:
                return term.makeTrue();
        }
    }

    @Override
    public SExpr visit(ArrayAccessExpr n, Object arg) {
        return term.and(
                n.getName().accept(this, arg),
                n.getIndex().accept(this, arg));
    }

    @Override
    public SExpr visit(ArrayCreationExpr n, Object arg) {
        //TODO
        return n.getInitializer().get().accept(this, arg);
    }

    @Override
    public SExpr visit(ArrayInitializerExpr n, Object arg) {
        List<SExpr> seq = n.getValues().stream().map(it -> it.accept(this, arg)).collect(Collectors.toList());
        return term.and(seq);
    }

    @Override
    public SExpr visit(AssignExpr n, Object arg) {
        return term.makeFalse();
    }

    @Override
    public SExpr visit(BinaryExpr n, Object arg) {
        switch (n.getOperator()) {
            case IMPLICATION:
                BinaryExpr be = new BinaryExpr(
                        new UnaryExpr(n.getLeft(), UnaryExpr.Operator.LOGICAL_COMPLEMENT),
                        n.getRight(), BinaryExpr.Operator.OR);
                return be.accept(this, arg);
            case DIVIDE:
            case REMAINDER:
                SExpr fml = n.getRight().accept(smtFormula, arg);
                return term.and(
                        n.getRight().accept(this, arg),
                        n.getLeft().accept(this, arg),
                        term.not(translator.binary(BinaryExpr.Operator.EQUALS,
                                fml, smtFormula.getTranslator().makeInt(BigInteger.ZERO))));
            default:
                return term.and(
                        n.getRight().accept(this, arg),
                        n.getLeft().accept(this, arg));
        }
    }

    @Override
    public SExpr visit(BooleanLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(CastExpr n, Object arg) {
        //TODO Type-check?
        return n.getExpression().accept(this, arg);
    }

    @Override
    public SExpr visit(CharLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(ClassExpr n, Object arg) {
        return term.makeFalse();
    }

    @Override
    public SExpr visit(DoubleLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(EnclosedExpr n, Object arg) {
        return wd(n.getInner());
    }

    @Override
    public SExpr visit(FieldAccessExpr n, Object arg) {
        return wd(n.getScope());
    }

    @Override
    public SExpr visit(InstanceOfExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public SExpr visit(IntegerLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(StringLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(SuperExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(ThisExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(UnaryExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public SExpr visit(LambdaExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(MethodReferenceExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(TypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(SwitchExpr n, Object arg) {
        return term.and(wd(n.getSelector()));
    }

    @Override
    public SExpr visit(TextBlockLiteralExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(PatternExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(JmlQuantifiedExpr n, Object arg) {
        /*The quantified-expression is well-defined iff the two sub-expressions are well-defined. For a quantifier Q*/
        List<SExpr> seq = n.getExpressions().stream()
                .map(it -> it.accept(this, arg))
                .collect(Collectors.toList());

        Expression r = n.getExpressions().get(0);
        Expression v = n.getExpressions().get(0);

        List<SExpr> args = new ArrayList<>();

        if (JmlQuantifiedExpr.JmlDefaultBinder.CHOOSE.equals(n.getBinder())) {
            return term.and(
                    term.forall(args, wd(r)),
                    term.forall(args, term.impl(valueOf(r), wd(v))),
                    term.exists(args, term.and(
                            valueOf(r),
                            valueOf(v))));
        }
        return term.and(
                term.forall(args, wd(r)),
                term.forall(args, term.impl(valueOf(r), wd(v))));
    }

    private SExpr valueOf(Expression e) {
        return e.accept(smtFormula, null);
    }

    private SExpr wd(Expression e) {
        return e.accept(this, null);
    }

    @Override
    public SExpr visit(JmlExpressionStmt n, Object arg) {
        return wd(n.getExpression());
    }

    @Override
    public SExpr visit(JmlLabelExpr n, Object arg) {
        return wd(n.getExpression());
    }

    @Override
    public SExpr visit(JmlLetExpr n, Object arg) {
        return term.and(wd(n.getBody())  /* TODO  arguments */, term.makeTrue());
    }

    @Override
    public SExpr visit(JmlClassExprDeclaration n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(JmlTypeExpr n, Object arg) {
        return term.makeTrue();
    }

    @Override
    public SExpr visit(JmlMultiExprClause n, Object arg) {
        return term.and(n.getExpressions().stream().map(this::wd).collect(Collectors.toList()));
    }

    @Override
    public SExpr visit(MethodCallExpr n, Object arg) {
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

        List<SExpr> seq = n.getArguments().stream()
                .map(it -> it.accept(this, arg))
                .collect(Collectors.toList());
        return term.and(seq);
    }
}
