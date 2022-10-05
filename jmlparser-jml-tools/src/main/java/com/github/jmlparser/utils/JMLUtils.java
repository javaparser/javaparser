package com.github.jmlparser.utils;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JMLUtils {

    public static final String GENERATED_COMBINED = "_generated_combined_";

    public static Expression unroll(JmlMultiCompareExpr n) {
        Expression r;
        if (n.getExpressions().isEmpty()) {
            r = new BooleanLiteralExpr(true);
        } else if (n.getExpressions().size() == 1) {
            r = n.getExpressions().get(0);
        } else {
            Expression e = null;
            for (int i = 0; i < n.getExpressions().size() - 1; i++) {
                BinaryExpr cmp = new BinaryExpr(
                        n.getExpressions().get(i).clone(),
                        n.getExpressions().get(i + 1).clone(),
                        n.getOperators().get(i));
                e = e == null ? cmp : new BinaryExpr(e, cmp, BinaryExpr.Operator.AND);
            }
            r = e;
        }
        r.setParentNode(n.getParentNode().orElse(null));
        return r;
    }

    public static void unroll(NodeList<JmlContract> old) {
        if (old.isEmpty()) return;
        var target = new ArrayList<JmlContract>(128);
        for (JmlContract c : old) {
            target.addAll(unroll(c));
        }
        old.clear();
        old.addAll(target);
    }

    private static List<JmlContract> unroll(JmlContract c) {
        if (c.getSubContracts().isEmpty())
            return Collections.singletonList(c);
        var seq = c.getSubContracts().stream()
                .flatMap(e -> unroll(e).stream())
                .toList();
        for (var sub : seq) {
            for (JmlClause clause : c.getClauses()) {
                sub.getClauses().add(clause.clone());
            }
        }
        return seq;
    }

    public static JmlContract createJointContract(NodeList<JmlContract> m) {
        var find = m.stream()
                .filter(name ->
                        name.getName().map(simpleName ->
                                        simpleName.asString().equals(GENERATED_COMBINED))
                                .orElse(false)).findFirst();
        if (find.isPresent())
            return find.get();

        unroll(m);

        var contract = new JmlContract();
        contract.setName(new SimpleName(GENERATED_COMBINED));
        //TODO weigl combine all requires, ensures ... clauses
        m.add(contract);
        return contract;
    }
}
