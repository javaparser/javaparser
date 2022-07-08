package com.github.jmlparser.wd;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import org.sosy_lab.java_smt.api.Formula;

import java.math.BigInteger;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public interface Translator {
    Formula binary(BinaryExpr.Operator operator, Formula left, Formula right);

    Formula makeChar(CharLiteralExpr n);

    Formula unary(UnaryExpr.Operator operator, Formula accept);

    Formula makeLong(LongLiteralExpr n);

    Formula makeInt(IntegerLiteralExpr n);

    Formula makeInt(BigInteger i);

    Formula makeIntVar();

    default List<? extends Formula> getVariable(NodeList<Parameter> variables) {
        return variables.stream().map(this::getVariable).collect(Collectors.toList());
    }

    Formula getVariable(Parameter jmlBoundVariable);

    Formula conditional(Formula accept, Formula accept1, Formula accept2);
}
