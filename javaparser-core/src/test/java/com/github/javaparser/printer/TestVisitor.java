package com.github.javaparser.printer;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

public class TestVisitor extends PrettyPrintVisitor {

    public TestVisitor(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        super(prettyPrinterConfiguration);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final Void arg) {
        printer.print("test");
    }
}