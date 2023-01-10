package com.github.jmlparser.utils;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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

    public static Type resolvedType2Type(ResolvedType type) {
        if (type.isPrimitive()) {
            ResolvedPrimitiveType rType = type.asPrimitive();
            return new PrimitiveType(
                    switch (rType) {
                        case BYTE -> PrimitiveType.Primitive.BYTE;
                        case SHORT -> PrimitiveType.Primitive.SHORT;
                        case CHAR -> PrimitiveType.Primitive.CHAR;
                        case INT -> PrimitiveType.Primitive.INT;
                        case LONG -> PrimitiveType.Primitive.LONG;
                        case BOOLEAN -> PrimitiveType.Primitive.BOOLEAN;
                        case FLOAT -> PrimitiveType.Primitive.FLOAT;
                        case DOUBLE -> PrimitiveType.Primitive.DOUBLE;
                    }
            );
        }

        if (type.isArray()) {
            ResolvedArrayType aType = type.asArrayType();
            return new ArrayType(resolvedType2Type(aType.getComponentType()));
        }

        if (type.isReferenceType()) {
            var rType = type.asReferenceType();
            return new ClassOrInterfaceType(rType.getQualifiedName());
        }

        throw new RuntimeException("Unsupported type");
    }
}
