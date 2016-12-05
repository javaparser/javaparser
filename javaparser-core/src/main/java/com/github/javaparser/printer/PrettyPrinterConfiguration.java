package com.github.javaparser.printer;

public class PrettyPrinterConfiguration {
    private boolean printComments = true;
    private String indent = "    ";

    public String getIndent() {
        return indent;
    }

    public PrettyPrinterConfiguration setIndent(String indent) {
        this.indent = indent;
        return this;
    }

    public boolean isPrintComments() {
        return printComments;
    }

    public PrettyPrinterConfiguration setPrintComments(boolean printComments) {
        this.printComments = printComments;
        return this;
    }
}
