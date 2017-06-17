package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;

/**
 * @deprecated this is a work in progress.
 */
@Deprecated
public class AsciiArtPrinter {
    public String output(Node node) {
        return "root (BinaryExpr)\n" +
                "\toperator: PLUS\n" +
                "\tleft (IntegerLiteralExpr)\n" +
                "\t\tvalue: 1\n" +
                "\tright (MethodCallExpr)\n" +
                "\t\tname (SimpleName)\n" +
                "\t\t\tidentifier: a\n" +
                "\t\targuments (IntegerLiteralExpr)\n" +
                "\t\t\tvalue: 1\n" +
                "\t\targuments (IntegerLiteralExpr)\n" +
                "\t\t\tvalue: 1\n";
    }
}
