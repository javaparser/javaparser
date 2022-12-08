package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;


public class Issue2592Test extends AbstractLexicalPreservingTest {

    @Test
    public void testLPP() {

        considerCode("public class A {" +
                "  public void m(final int a_original, int b) {" +
                "  }" +
                "} ");
        Optional<MethodDeclaration> md = cu.findFirst(MethodDeclaration.class);
        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));

        //all parameters have parent nodes here
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));


        //add a third parameter
        md.get().addParameter("String", "c_brand_new");

        //seems like we can add a parameter fine (and all of the parents still assigned)
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));


//        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        Parameter p1 = md.get().getParameter(0);
        Parameter p2 = new Parameter(p1.getModifiers(), p1.getType(), new SimpleName("a_renamed"));

        //here we replace a parameter
        boolean isReplaced = md.get().replace(p1, p2);
        assertTrue(isReplaced); //the replacement seemed to work


        //...however when we replaced the parent nodes (for the replaced node AND the added node (after the replaced node) now null
//        md.get().getParameters().forEach(p -> System.out.println(p + " parent " + p.getParentNode().isPresent()));
        assertTrue(md.get().getParameters().stream().allMatch(p -> p.getParentNode().isPresent()));
    }

}
