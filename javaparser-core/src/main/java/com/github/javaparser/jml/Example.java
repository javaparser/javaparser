package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.IntSummaryStatistics;
import java.util.stream.IntStream;

/**
 * @author Alexander Weigl
 * @version 1 (2/26/21)
 */
public class Example {
    public static void main(String[] args) throws FileNotFoundException {
        /*GeneratedJavaParserTokenManager manager = new GeneratedJavaParserTokenManager(
                new SimpleCharStream(new StreamProvider(new FileReader(
                        "/home/weigl/work/javaparser/JmlExample.java"))));
        //new SimpleCharStream(new StringProvider("//@ test\n")));
        manager.setStoreTokens(true);

        Token t;
        int cnt = 0;
        do {
            t = manager.getNextToken();
            System.out.format("%3d: (%3d) %s%n", cnt++, t.kind, t);
        } while (t.kind != GeneratedJavaParserConstants.EOF);
        */

        ParserConfiguration config = new ParserConfiguration();
        config.setDoNotAssignCommentsPrecedingEmptyLines(false);
        config.setAttributeComments(true);
        config.setProcessJml(true);
        JavaParser jpb = new JavaParser(config);


        IntStream timings = IntStream.rangeClosed(0, 0)
                .map(i -> {
                    long start = System.currentTimeMillis();
                    try {
                        ParseResult<CompilationUnit> result =
                                jpb.parse(new File("/home/weigl/work/javaparser/JmlExample.java"));
                    } catch (FileNotFoundException e) {
                        e.printStackTrace();
                    }
                    long stop = System.currentTimeMillis();
                    return (int) (stop - start);
                });

        IntSummaryStatistics stat = timings.summaryStatistics();
        System.out.println(stat);

        ParseResult<CompilationUnit> result =
                jpb.parse(new File("/home/weigl/work/javaparser/JmlExample.java"));

        System.out.println(result);
        result.getResult().ifPresent(it -> {
            DefaultPrinterConfiguration c = new DefaultPrinterConfiguration();
            DefaultPrettyPrinter v = new DefaultPrettyPrinter(c);
            System.out.println(v.print(it));
        });
    }
}
