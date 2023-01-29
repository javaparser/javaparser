package com.github.jmlparser.smt;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlDefaultBinder;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.jmlparser.smt.model.SAtom;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SmtType;
import com.github.jmlparser.utils.JMLUtils;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public class JmlExpr2Smt extends GenericVisitorAdapter<SExpr, Object> {
    private final ArithmeticTranslator translator;
    private static final SmtTermFactory termFactory = SmtTermFactory.INSTANCE;

    private final SmtQuery smtLog;
    private VariableStack boundedVars = new VariableStack();

    public JmlExpr2Smt(SmtQuery smtLog, ArithmeticTranslator translator) {
        this.smtLog = smtLog;
        this.translator = translator;
    }

    @Override
    public SExpr visit(ArrayAccessExpr n, Object arg) {
        SExpr array = n.getName().accept(this, arg);
        SExpr index = n.getIndex().accept(this, arg);
        ResolvedType rtype = n.calculateResolvedType();
        SmtType stype = translator.getType(rtype);
        return termFactory.select(stype, rtype, array, index);
    }

    @Override
    public SExpr visit(ArrayCreationExpr n, Object arg) {
        if (n.getInitializer().isPresent())
            return n.getInitializer().get().accept(this, arg);

        String name = "anon_array_" + (++anonCnt);
        final ResolvedType rType = n.calculateResolvedType();
        SmtType type = translator.getType(rType);
        smtLog.declareConst(name, type);
        final SExpr var = termFactory.var(type, rType, name);
        final SExpr zero = translator.makeInt(BigInteger.ZERO);
        final SExpr arrayLength = translator.arrayLength(var);

        List<SExpr> boundedVars = new ArrayList<>();
        SExpr accessLevel = var;
        for (int i = 0; i < n.getLevels().size(); i++) {
            ArrayCreationLevel level = n.getLevels().get(i);
            if (i == 0) {
                if (level.getDimension().isPresent()) {
                    final SExpr length = level.getDimension().get().accept(this, arg);
                    smtLog.addAssert(termFactory.equality(arrayLength, length));
                } else {
                    smtLog.addAssert(termFactory.lessOrEquals(zero, arrayLength, true));
                }
            } else {
                if (level.getDimension().isPresent()) {
                    final SExpr length = level.getDimension().get().accept(this, arg);
                    smtLog.addAssert(
                            termFactory.forall(boundedVars,
                                    termFactory.equality(translator.arrayLength(accessLevel), length)));
                } else {
                    smtLog.addAssert(
                            termFactory.forall(boundedVars,
                                    termFactory.lessOrEquals(zero, translator.arrayLength(accessLevel), true)));
                }
            }
            boundedVars.add(termFactory.binder(SmtType.INT, "idx" + i));
            accessLevel = termFactory.select(null, null, accessLevel,
                    termFactory.var(SmtType.INT, null, "idx" + i));
        }
        return var;
    }

    @Override
    public SExpr visit(ArrayInitializerExpr n, Object arg) {
        String name = "anon_array_" + (++anonCnt);
        List<SExpr> seq = n.getValues().stream().map(it -> it.accept(this, arg)).toList();
        SmtType.Array myType = new SmtType.Array(SmtType.INT, seq.get(0).getSmtType());
        smtLog.declareConst(name, myType);
        SExpr var = termFactory.var(myType, null, name);
        for (int i = 0; i < seq.size(); i++) {
            smtLog.addAssert(
                    //(store ary idx sub)
                    termFactory.store(var, translator.makeInt(i), seq.get(i))
            );
        }

        SExpr zero = translator.makeInt(0);
        final SExpr length = translator.arrayLength(var);
        smtLog.addAssert(termFactory.equality(length, translator.makeInt(n.getValues().size())));
        return var;
    }

    @Override
    public SExpr visit(AssignExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(BinaryExpr n, Object arg) {
        SExpr left = n.getLeft().accept(this, arg);
        SExpr right = n.getRight().accept(this, arg);
        return translator.binary(n.getOperator(), left, right);
    }

    @Override
    public SExpr visit(ThisExpr n, Object arg) {
        return termFactory.makeThis();
    }

    @Override
    public SExpr visit(SuperExpr n, Object arg) {
        return termFactory.makeSuper();
    }

    @Override
    public SExpr visit(NameExpr n, Object arg) {
        ResolvedValueDeclaration resolved = n.resolve();
        ResolvedType rType = resolved.getType();
        final SmtType type = translator.getType(rType);
        if (!isBound(n.getNameAsString())) {
            smtLog.declareConst(n.getNameAsString(), type);
        }
        return termFactory.var(type, rType, n.getNameAsString());
    }

    private boolean isBound(String nameAsString) {
        return boundedVars.contains(nameAsString);
    }


    @Override
    public SExpr visit(NullLiteralExpr n, Object arg) {
        return termFactory.makeNull();
    }

    @Override
    public SExpr visit(BooleanLiteralExpr n, Object arg) {
        return translator.makeBoolean(n.getValue());
    }

    @Override
    public SExpr visit(CastExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(CharLiteralExpr n, Object arg) {
        return translator.makeChar(n);
    }

    @Override
    public SExpr visit(ClassExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(ConditionalExpr n, Object arg) {
        return termFactory.ite(
                n.getCondition().accept(this, arg),
                n.getThenExpr().accept(this, arg),
                n.getElseExpr().accept(this, arg));
    }

    @Override
    public SExpr visit(DoubleLiteralExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(FieldAccessExpr n, Object arg) {
        ResolvedType scopeType = n.getScope().calculateResolvedType();
        ResolvedType javaType = n.calculateResolvedType();
        SmtType stype = translator.getType(javaType);
        SExpr obj = n.getScope().accept(this, arg);

        if (n.getNameAsString().equals("length") && scopeType.isArray()) {
            return translator.arrayLength(obj);
        }

        return termFactory.fieldAccess(javaType, stype, n.getNameAsString(), obj);
    }

    @Override
    public SExpr visit(InstanceOfExpr n, Object arg) {
        ResolvedType leftType = n.getExpression().calculateResolvedType();
        ResolvedType rightType = n.getType().resolve();

        //TODO weigl return leftType.asReferenceType()
        //Pattern matching
        return termFactory.makeTrue();
    }

    @Override
    public SExpr visit(IntegerLiteralExpr n, Object arg) {
        return translator.makeInt(n);
    }

    @Override
    public SExpr visit(LongLiteralExpr n, Object arg) {
        return translator.makeLong(n);
    }

    @Override
    public SExpr visit(MethodCallExpr n, Object arg) {
        var method = n.resolve();
        var variable = translator.makeVar(method.getReturnType());
        final var ast = method.toAst();
        if (ast.isPresent() && ast.get() instanceof NodeWithContracts<?> hasContracts) {
            var contract =
                    JMLUtils.createJointContract(hasContracts.getContracts().get());
            //TODO weigl add assertion for the return variable
            //TODO weigl add assertion for each parameter
            // smtLog.addAssert();
        }
        return variable;
    }

    int anonCnt;

    @Override
    public SExpr visit(ObjectCreationExpr n, Object arg) {
        final String name = "anon" + (++anonCnt);
        smtLog.declareConst(name, SmtType.JAVA_OBJECT);
        SExpr var = termFactory.var(SmtType.JAVA_OBJECT, null, name);
        smtLog.addAssert(termFactory.nonNull(var));
        return var;
    }

    @Override
    public SExpr visit(StringLiteralExpr n, Object arg) {
        return new SAtom(SmtType.STRING, null, "\"" + n.asString() + "\"");
    }

    @Override
    public SExpr visit(UnaryExpr n, Object arg) {
        return translator.unary(n.getOperator(), n.getExpression().accept(this, arg));
    }

    @Override
    public SExpr visit(LambdaExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(TypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(SwitchExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(TextBlockLiteralExpr n, Object arg) {
        return new SAtom(SmtType.STRING, null, "\"" + n.asString() + "\"");
    }

    @Override
    public SExpr visit(PatternExpr n, Object arg) {
        return super.visit(n, arg);
    }

    @Override
    public SExpr visit(JmlQuantifiedExpr n, Object arg) {
        try (TruncateStack ignored = boundedVars.bind(n.getVariables())) {
            switch ((JmlDefaultBinder) n.getBinder()) {
                case FORALL:
                    Expression e =
                            n.getExpressions().size() == 2
                                    ? new BinaryExpr(n.getExpressions().get(0), n.getExpressions().get(1), BinaryExpr.Operator.IMPLICATION)
                                    : n.getExpressions().get(0);
                    e.setParentNode(n);
                    return termFactory.forall(
                            translator.getVariable(n.getVariables()),
                            e.accept(this, arg));
                case EXISTS:
                    Expression e1 =
                            n.getExpressions().size() == 2
                                    ? new BinaryExpr(n.getExpressions().get(0), n.getExpressions().get(1), BinaryExpr.Operator.AND)
                                    : n.getExpressions().get(0);
                    e1.setParentNode(n);
                    return termFactory.forall(
                            translator.getVariable(n.getVariables()),
                            e1.accept(this, arg));
                case BSUM:
                case MIN:
                case MAX:
                case PRODUCT:
                    return translator.makeIntVar();
                default:
                    return null;
            }
        }
    }

    @Override
    public SExpr visit(JmlLabelExpr n, Object arg) {
        return n.getExpression().accept(this, arg);
    }

    @Override
    public SExpr visit(JmlLetExpr n, Object arg) {
        try (TruncateStack ignored = boundedVars.bind(n.getVariables())) {
            List<SExpr> vars = new ArrayList<>();
            for (VariableDeclarator variable : n.getVariables().getVariables()) {
                vars.add(termFactory.list(null, null, variable.getNameAsString(),
                        variable.getInitializer().get().accept(this, arg)));
            }
            SExpr body = n.getBody().accept(this, arg);
            return termFactory.let(vars, body);
        }
    }

    @Override
    public SExpr visit(JmlMultiCompareExpr n, Object arg) {
        return JMLUtils.unroll(n).accept(this, arg);
    }

    @Override
    public SExpr visit(JmlBinaryInfixExpr n, Object arg) {
        SExpr left = n.getLeft().accept(this, arg);
        SExpr right = n.getRight().accept(this, arg);
        return termFactory.list(null, null, n.getOperator().getIdentifier(), left, right);
    }

    @Override
    public SExpr visit(JmlTypeExpr n, Object arg) {
        return super.visit(n, arg);
    }

    public ArithmeticTranslator getTranslator() {
        return translator;
    }
}


class VariableStack {
    private final ArrayList<String> seq = new ArrayList<>(16);

    public TruncateStack bind(VariableDeclarationExpr variables) {
        int curPosition = seq.size();
        for (VariableDeclarator variable : variables.getVariables())
            seq.add(variable.getNameAsString());
        return () -> truncate(curPosition);
    }

    public TruncateStack bind(NodeList<Parameter> variables) {
        int curPosition = seq.size();
        for (Parameter variable : variables)
            seq.add(variable.getNameAsString());
        return () -> truncate(curPosition);
    }

    private void truncate(int curPosition) {
        while (seq.size() > curPosition) {
            seq.remove(seq.size() - 1);
        }
    }

    public boolean contains(String nameAsString) {
        return seq.contains(nameAsString);
    }

}

interface TruncateStack extends AutoCloseable {
    @Override
    void close();
}
