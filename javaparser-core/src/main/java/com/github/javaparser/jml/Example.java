package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
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
        JavaParser jpb = new JavaParser();
        var result = jpb.parse(new File("./JmlExample.java"));

        JmlPipeline jmlPipeline = new JmlPipeline();
        System.out.println(result);
        result.getResult().ifPresent(it -> {
            jmlPipeline.processJml(it);
            final var c = new DefaultPrinterConfiguration();
            var v = new DefaultPrettyPrinter(c);
            System.out.println(v.print(it));
        });
    }
}
