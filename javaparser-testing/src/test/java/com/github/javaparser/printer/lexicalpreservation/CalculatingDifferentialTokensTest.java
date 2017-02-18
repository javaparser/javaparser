package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.*;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;

public class CalculatingDifferentialTokensTest extends AbstractLexicalPreservingTest {



//    @Test
//    public void diffInASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
//        String code = "class A { void foo(char p1, int p2) {} }";
//        considerCode(code);
//
//        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
//
//        List<CompulsoryElement> preTokens = findCompulsoryTokens(m);
//        preTokens.forEach(System.out::println);
//
//        m.getParameters().remove(0);
//
//        System.out.println("AFTER");
//        List<CompulsoryElement> postTokens = findCompulsoryTokens(m);
//        postTokens.forEach(System.out::println);
//
//        //assertEquals("void foo(int p2) {}", lpp.print(m));
//    }


}
