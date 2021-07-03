package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;

import java.io.File;
import java.io.FileNotFoundException;

/**
 * @author Alexander Weigl
 * @version 1 (2/26/21)
 */
public class Example {
    public static void main(String[] args) throws FileNotFoundException {
        /*
        GeneratedJavaParserTokenManager manager = new GeneratedJavaParserTokenManager(
                new SimpleCharStream(new StringProvider("//@ test\n")));
        manager.ReInit(new SimpleCharStream(new StringProvider("//@ test\n")));
        manager.setStoreTokens(true);

        System.out.println(manager.getNextToken().kind);
        System.out.println(manager.getNextToken().kind);
        System.out.println(manager.getNextToken().kind);
        System.out.println(manager.getNextToken().kind);
        System.out.println(manager.getNextToken());
        */

        JavaParser jpb = new JavaParser();
        ParseResult<CompilationUnit> result = jpb.parse(new File("/home/weigl/work/javaparser/jmlparser-jml-tests/src/test/resources/fullexamples/key/firstTouch/08-Java5/src/For.java"));

        System.out.println(result);
        result.getResult().ifPresent(it -> {
            DefaultPrinterConfiguration c = new DefaultPrinterConfiguration();
            DefaultPrettyPrinter v = new DefaultPrettyPrinter(c);
            System.out.println(v.print(it));
        });
    }
}
