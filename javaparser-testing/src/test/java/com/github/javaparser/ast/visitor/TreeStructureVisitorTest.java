package com.github.javaparser.ast.visitor;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.format.Format;
import com.github.javaparser.utils.format.FormatInstructions;
import com.github.javaparser.utils.format.FormatInstructionsFactory;

/**
 * A set of tests verifying the output of baked-in formatting instructions.
 *
 * @see TreeStructureVisitorGenerator
 * @see FormatInstructions
 * @version 3.1.0
 * @since 3.1.0
 * @author Danny van Bruggen
 * @author Ryan Beckett
 *
 */
public class TreeStructureVisitorTest {

    private static final String src = "package mypackage;\n" +
            "\n" +
            "public final class MyClass {\n" +
            "\n" +
            "    public void myMethod() {\n" +
            "        if ((hello() == \"abc\" && foo() == \"def\" && 1 == 1) || (2 == 2)) {\n" +
            "        }\n" +
            "    }\n" +
            "    public void myMethod2() {}\n" +
            "    public void myMethod3() {}\n" +
            "}";
    private static final CompilationUnit cu = JavaParser.parse(src);

    @Test
    public void dumpDefault() {
        TreeStructureVisitor tsv = new TreeStructureVisitor();
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

    @Test
    public void dumpDefaultWithNoIndent() {
        TreeStructureVisitor tsv = new TreeStructureVisitor(false, true);
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

    @Test
    public void dumpDefaultWithNoNewline() {
        TreeStructureVisitor tsv = new TreeStructureVisitor(true, false);
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

    @Test
    public void dumpDefaultWithNoIdentNorNewline() {
        TreeStructureVisitor tsv = new TreeStructureVisitor(false, false);
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

    @Test
    public void dumpXML() {
        TreeStructureVisitor tsv = new TreeStructureVisitor(
                FormatInstructionsFactory.getFormatInstructions(Format.XML));
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

    @Test
    public void dumpJSON() {
        TreeStructureVisitor tsv = new TreeStructureVisitor(
                FormatInstructionsFactory.getFormatInstructions(Format.JSON));
        cu.accept(tsv, 0);
        System.out.println(tsv.getResult() + "\n----------------------");
    }

}