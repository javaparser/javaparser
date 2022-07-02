package com.github.jmlparser.wd;

import com.github.javaparser.ast.JmlBoundVariable;
import com.github.javaparser.ast.NodeList;
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

    default List<? extends Formula> getVariable(NodeList<JmlBoundVariable> variables) {
        return variables.stream().map(this::getVariable0).collect(Collectors.toList());
    }

    Formula getVariable0(JmlBoundVariable jmlBoundVariable);

    Formula conditional(Formula accept, Formula accept1, Formula accept2);
}
