package com.github.jmlparser.stat;

import lombok.Data;

/**
 * @author Alexander Weigl
 * @version 1 (02.06.22)
 */
@Data
public class ExpressionCosts {
    private int sum = 1;
    private int minus = 1;
    private int divide = 1;
    private int mult = 1;
    private int mod = 1;
    private int land = 1;
    private int lor = 1;
    private int lnot = 1;
    private int band = 1;
    private int bor = 2;
    private int bnot = 1;
    private int quantor = 3;
    private int binderCostsPerVariable = 1;
    private int nullLiteral = 0;
    private int charLiteral = 0;
    private int stringLiteral = 0;
    private int integerLiteral = 0;
    private int longLiteral = 0;
    private int name = 0;
    private int methodCall = 2;
    private int conditional = 2;
    private int cast = 1;
    private int assign = 1;
    private int let = 1;
    private int compare = 1;
    private int _instanceof = 1;
}
