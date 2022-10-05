package com.github.jmlparser.smt;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SmtType;

import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public interface ArithmeticTranslator {
    SExpr binary(BinaryExpr.Operator operator, SExpr left, SExpr right);

    SExpr makeChar(CharLiteralExpr n);

    SExpr unary(UnaryExpr.Operator operator, SExpr accept);

    SExpr makeLong(LongLiteralExpr n);

    SExpr makeInt(IntegerLiteralExpr n);

    SExpr makeInt(BigInteger i);

    SExpr makeIntVar();

    default List<? extends SExpr> getVariable(NodeList<Parameter> variables) {
        return variables.stream().map(this::getVariable).collect(Collectors.toList());
    }

    SExpr getVariable(Parameter jmlBoundVariable);

    SExpr makeBoolean(boolean value);

    SmtType getType(ResolvedType asPrimitive);

    SExpr arrayLength(SExpr obj);

    SExpr makeInt(long i);

    SExpr makeVar(ResolvedType rtype);
}
