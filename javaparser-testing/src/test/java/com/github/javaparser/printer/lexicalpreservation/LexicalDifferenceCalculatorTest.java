package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class LexicalDifferenceCalculatorTest extends AbstractLexicalPreservingTest {

    @Test
    public void compilationUnitExampleOriginal() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, cu);
        assertEquals(2, csmOriginal.elements.size());
        assertEquals(new LexicalDifferenceCalculator.CsmChild(cu.getType(0)), csmOriginal.elements.get(0));
        assertEquals(new CsmToken(3), csmOriginal.elements.get(1));
    }

    @Test
    public void compilationUnitExampleWithPackageSet() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        PackageDeclaration packageDeclaration = new PackageDeclaration(new Name(new Name("foo"), "bar"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, cu, ObservableProperty.PACKAGE_DECLARATION, null, packageDeclaration);
        assertEquals(3, csmChanged.elements.size());
        assertEquals(new LexicalDifferenceCalculator.CsmChild(packageDeclaration), csmChanged.elements.get(0));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(cu.getType(0)), csmChanged.elements.get(1));
        assertEquals(new CsmToken(3), csmChanged.elements.get(2));
    }
}
