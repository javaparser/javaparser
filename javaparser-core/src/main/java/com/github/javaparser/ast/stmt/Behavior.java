package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.jml.JmlKeyword;

/**
 * @author Alexander Weigl
 * @version 1 (3/14/21)
 */
public enum Behavior implements Jmlish, JmlKeyword {
    NONE(""), BEHAVIOR("behavior"), NORMAL("normal_behavior"), EXCEPTIONAL("exceptional_behavior"),
    MODEL("model_behavior"), BREAK("break_behavior"), CONTINUE("continue_behavior"), RETURN("return_behavior");

    private final String symbol;

    Behavior(String symbol) {
        this.symbol = symbol;
    }

    @Override
    public String jmlSymbol() {
        return symbol;
    }
}
