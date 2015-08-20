package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.visitor.DumpVisitor;

import java.io.File;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

/**
 * Created by federico on 05/09/15.
 */
public class PerformanceCalc {

    private static boolean dumpToFile = true;

    public static void main(String[] args) {

        // startup
        for (int i=0; i< 5; i++) {
            parseEverything();
        }

        long start = System.currentTimeMillis();
        for (int i=0; i< 10; i++) {
            parseEverything();
        }
        long end = System.currentTimeMillis();
        System.out.println(end - start);
        System.out.println("OK : " + ok);
        System.out.println("KO : " + ko);
    }

    private static void parseEverything() {
        parse(new File("/home/federico/repos/idea/java/compiler"));
        parse(new File("/home/federico/repos/idea/java/debugger"));
        parse(new File("/home/federico/repos/idea/java/mockJDK-1.8"));
        parse(new File("/home/federico/repos/idea/java/java-runtime"));
        parse(new File("/home/federico/Downloads/openjdk/jaxp/src"));
        parse(new File("/home/federico/repos/walkmod-core"));
    }

    private static int ok = 0;
    private static int ko = 0;

    private static void parse(File file) {
        //System.out.println("PARSE " + file);
        if (file.isDirectory()) {
            for (File child : file.listFiles()) {
                parse(child);
            }
        } else {
            try {
                if (file.getName().endsWith(".java")) {
                    CompilationUnit cu = JavaParser.parse(file);
                    if (dumpToFile) {
                        DumpVisitor dumpVisitor = new DumpVisitor();
                        cu.accept(dumpVisitor, null);
                        Files.write(Paths.get("dump.txt"), dumpVisitor.getSource().getBytes(), StandardOpenOption.CREATE);
                    }
                    ok++;
                }
            } catch (Throwable e) {
                //System.err.println("SKIP " + file.getName());
                ko++;
            }
        }
    }

}
