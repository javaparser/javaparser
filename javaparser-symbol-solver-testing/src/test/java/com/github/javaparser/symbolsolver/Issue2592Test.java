package com.github.javaparser.symbolsolver;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertTrue;


public class Issue2592Test {

    @Test
    public void testLPP() {

        String s = "public class A {" +
                "  public void m(final int a, int b) {" +
                "  }" +
                "} ";
        CompilationUnit cu = StaticJavaParser.parse(s);
        Optional<MethodDeclaration> md = cu.findFirst(MethodDeclaration.class);
        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));

        //this seems to be doing nasty things to parent nodes (after a change happens)
        LexicalPreservingPrinter.setup(cu);

        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));

        md.get().addParameter("Added", "a");

        //seems like we can add a parameter fine (and all of the parents still assigned)
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));


        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        Parameter p1 = md.get().getParameter(0);
        Parameter p2 = new Parameter(p1.getModifiers(), p1.getType(), new SimpleName("a1"));

        //here we replace a parameter
        boolean isReplaced = md.get().replace(p1, p2);
        assertTrue(isReplaced); //the replacement seemed to work
        System.out.println(cu.toString()); //this looks right


        //...however when we replaced the parent nodes (for the replaced node AND the added node (after the replaced node) now null
        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));
    }

}
