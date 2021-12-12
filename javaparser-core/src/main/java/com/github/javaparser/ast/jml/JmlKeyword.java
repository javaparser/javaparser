package com.github.javaparser.ast.jml;

import com.github.javaparser.printer.Stringable;

/**
 * @author Alexander Weigl
 * @version 1 (3/20/21)
 */
public interface JmlKeyword extends Stringable {
    String jmlSymbol();

    @Override
    default String asString() {
        return jmlSymbol();
    }
}
