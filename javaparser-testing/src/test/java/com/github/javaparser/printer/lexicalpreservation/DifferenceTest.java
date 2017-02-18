package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.HashCodeVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;

public class DifferenceTest {

    @Test
    public void calculateDifferenceEmpty() {
        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        Difference diff = Difference.calculate(a, b);
        assertEquals(0, diff.getElements().size());
    }

    @Test
    public void calculateDifferenceAIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmElement[]{
                        new CsmToken(ASTParserConstants.LPAREN),
                        new LexicalDifferenceCalculator.CsmChild(n1),
                        new CsmToken(ASTParserConstants.RPAREN),
                        new LexicalDifferenceCalculator.CsmChild(n2)
                }
        ));
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(Difference.DifferenceElement.added(new CsmToken(ASTParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(Difference.DifferenceElement.added(new LexicalDifferenceCalculator.CsmChild(n1)), diff.getElements().get(1));
        assertEquals(Difference.DifferenceElement.added(new CsmToken(ASTParserConstants.RPAREN)), diff.getElements().get(2));
        assertEquals(Difference.DifferenceElement.added(new LexicalDifferenceCalculator.CsmChild(n2)), diff.getElements().get(3));
    }

    @Test
    public void calculateDifferenceBIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmElement[]{
                        new CsmToken(ASTParserConstants.LPAREN),
                        new LexicalDifferenceCalculator.CsmChild(n1),
                        new CsmToken(ASTParserConstants.RPAREN),
                        new LexicalDifferenceCalculator.CsmChild(n2)
                }
        ));
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(Difference.DifferenceElement.removed(new CsmToken(ASTParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(Difference.DifferenceElement.removed(new LexicalDifferenceCalculator.CsmChild(n1)), diff.getElements().get(1));
        assertEquals(Difference.DifferenceElement.removed(new CsmToken(ASTParserConstants.RPAREN)), diff.getElements().get(2));
        assertEquals(Difference.DifferenceElement.removed(new LexicalDifferenceCalculator.CsmChild(n2)), diff.getElements().get(3));
    }
}
