package com.github.javaparser.printer;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

/**
 * Created by bresai on 2016/12/19.
 */
public class TestVisitor extends PrettyPrintVisitor {

    public TestVisitor(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        super(prettyPrinterConfiguration);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final Void arg) {
        printer.print("test");
    }
}