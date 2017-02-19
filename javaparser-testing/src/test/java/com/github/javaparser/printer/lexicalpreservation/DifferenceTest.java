package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.HashCodeVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;

import static com.github.javaparser.printer.lexicalpreservation.Difference.DifferenceElement.added;
import static com.github.javaparser.printer.lexicalpreservation.Difference.DifferenceElement.kept;
import static com.github.javaparser.printer.lexicalpreservation.Difference.DifferenceElement.removed;
import static org.junit.Assert.assertEquals;

public class DifferenceTest extends AbstractLexicalPreservingTest {

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
                        new CsmChild(n1),
                        new CsmToken(ASTParserConstants.RPAREN),
                        new CsmChild(n2)
                }
        ));
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(added(new CsmToken(ASTParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(added(new CsmChild(n1)), diff.getElements().get(1));
        assertEquals(added(new CsmToken(ASTParserConstants.RPAREN)), diff.getElements().get(2));
        assertEquals(added(new CsmChild(n2)), diff.getElements().get(3));
    }

    @Test
    public void calculateDifferenceBIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmElement[]{
                        new CsmToken(ASTParserConstants.LPAREN),
                        new CsmChild(n1),
                        new CsmToken(ASTParserConstants.RPAREN),
                        new CsmChild(n2)
                }
        ));
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(removed(new CsmToken(ASTParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(removed(new CsmChild(n1)), diff.getElements().get(1));
        assertEquals(removed(new CsmToken(ASTParserConstants.RPAREN)), diff.getElements().get(2));
        assertEquals(removed(new CsmChild(n2)), diff.getElements().get(3));
    }

    @Test
    public void compilationUnitExampleWithPackageSetDiff() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        PackageDeclaration packageDeclaration = new PackageDeclaration(new Name(new Name("foo"), "bar"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, cu);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, cu, ObservableProperty.PACKAGE_DECLARATION, null, packageDeclaration);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(3, diff.getElements().size());
        assertEquals(added(new CsmChild(packageDeclaration)), diff.getElements().get(0));
        assertEquals(kept(new CsmChild(cu.getType(0))), diff.getElements().get(1));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(2));
    }

    @Test
    public void annotationDeclarationExampleWithModifierAdded() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, EnumSet.noneOf(Modifier.class), EnumSet.of(Modifier.PUBLIC));
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(26, diff.getElements().size());
        assertEquals(added(new CsmToken(ASTParserConstants.PUBLIC)), diff.getElements().get(0));
        assertEquals(added(new CsmToken(1)), diff.getElements().get(1));
        assertEquals(kept(new CsmToken(ASTParserConstants.AT)), diff.getElements().get(2));
        assertEquals(kept(new CsmToken(ASTParserConstants.INTERFACE)), diff.getElements().get(3));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(4));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(5));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(6));
        assertEquals(kept(new CsmToken(ASTParserConstants.LBRACE)), diff.getElements().get(7));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(8));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(9));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(10));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(11));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(12));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(13));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(14));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(15));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(16));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(17));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(18));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(19));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(20));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(21));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(22));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(23));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(24));
        assertEquals(kept(new CsmToken(ASTParserConstants.RBRACE)), diff.getElements().get(25));
    }

    @Test
    public void annotationDeclarationExampleWithNameChanged() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        SimpleName newName = new SimpleName("NewName");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.NAME,
                annotationDeclaration.getName(), newName);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(25, diff.getElements().size());
        assertEquals(kept(new CsmToken(ASTParserConstants.AT)), diff.getElements().get(0));
        assertEquals(kept(new CsmToken(ASTParserConstants.INTERFACE)), diff.getElements().get(1));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(2));
        assertEquals(removed(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(3));
        assertEquals(added(new CsmChild(newName)), diff.getElements().get(4));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(5));
        assertEquals(kept(new CsmToken(ASTParserConstants.LBRACE)), diff.getElements().get(6));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(7));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(8));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(9));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(10));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(11));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(12));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(13));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(14));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(15));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(16));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(17));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(18));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(19));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(20));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(21));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(22));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(23));
        assertEquals(kept(new CsmToken(ASTParserConstants.RBRACE)), diff.getElements().get(24));
    }

    @Test
    public void annotationDeclarationExampleWithJavadocAdded() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        JavadocComment comment = new JavadocComment("Cool this annotation!");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, null, comment);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(28, diff.getElements().size());
        int i = 0;
        assertEquals(added(new CsmToken(ASTParserConstants.JAVA_DOC_COMMENT, "/**Cool this annotation!*/")), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.RBRACE)), diff.getElements().get(i++));
    }

    @Test
    public void annotationDeclarationExampleWithJavadocRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example9_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, annotationDeclaration.getComment().get(), null);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(28, diff.getElements().size());
        int i = 0;
        assertEquals(removed(new CsmToken(ASTParserConstants.JAVA_DOC_COMMENT, "/**Cool this annotation!*/")), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.RBRACE)), diff.getElements().get(i++));
    }

    @Test
    public void annotationDeclarationExampleWithModifierRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, EnumSet.of(Modifier.PUBLIC), EnumSet.noneOf(Modifier.class));
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        assertEquals(26, diff.getElements().size());
        int i = 0;
        assertEquals(removed(new CsmToken(ASTParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(3)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.RBRACE)), diff.getElements().get(i++));
    }

    @Test
    public void removeDefaultValueInAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration md = considerAmd("int foo() default 10;");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(md, ObservableProperty.DEFAULT_VALUE, md.getDefaultValue(), null);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(kept(new CsmChild(md.getType())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(md.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(ASTParserConstants.DEFAULT)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(1)), diff.getElements().get(i++));
        assertEquals(removed(new CsmChild(md.getDefaultValue().get())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(ASTParserConstants.SEMICOLON)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    protected AnnotationMemberDeclaration considerAmd(String code) {
        considerCode("@interface AD { " + code + " }");
        return (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("AD").get().getMember(0);
    }
}
