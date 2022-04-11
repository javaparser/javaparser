package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

/**
 * @author Meghdoot Ojha
 */
public class JavaParserFactory {
    public static JavaParser getInstance(String context) {
        JavaParser parser = null;
        if (context == "IfStatementContext") {
            parser = new IfStatementContext();
            return parser;
        }
        if (context == "StatementContext") {
            parser = (JavaParser) new StatementContext();
            return parser;
        }if (context == "ForStatementContext") {
            parser = new ForStatementContext();
            return parser;
        }if (context == "FieldAccessContext") {
            parser = new FieldAccessContext();
            return parser;
        }if (context == "UnaryExprContext") {
            parser = (JavaParser) new UnaryExprContext();
            return parser;
        }if (context == "VariableDeclaratorContext") {
            parser = (JavaParser) new VariableDeclaratorContext();
            return parser;
        }
        return parser;
    }

}
