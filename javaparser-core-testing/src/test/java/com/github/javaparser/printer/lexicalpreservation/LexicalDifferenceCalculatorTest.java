package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.TokenTypes.spaceTokenKind;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class LexicalDifferenceCalculatorTest extends AbstractLexicalPreservingTest {

    @Test
    public void compilationUnitExampleOriginal() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, cu);
        assertEquals(2, csmOriginal.elements.size());
        assertEquals(new LexicalDifferenceCalculator.CsmChild(cu.getType(0)), csmOriginal.elements.get(0));
        assertEquals(new CsmToken(eolTokenKind()), csmOriginal.elements.get(1));
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
        assertEquals(new CsmToken(eolTokenKind()), csmChanged.elements.get(2));
    }

    @Test
    public void annotationDeclarationModifiersExampleOriginal() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void annotationDeclarationModifiersExampleModified() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, EnumSet.noneOf(Modifier.class), EnumSet.of(Modifier.PUBLIC));
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.PUBLIC), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void annotationDeclarationNameExampleModified() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        SimpleName newName = new SimpleName("NewName");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.NAME,
                annotationDeclaration.getName(), newName);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(newName), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void annotationDeclaratioJavadocExampleOriginal() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.PUBLIC), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void annotationDeclaratioJavadocExampleAddingJavadoc() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        JavadocComment comment = new JavadocComment("Cool this annotation!");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, null, comment);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.PUBLIC), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new LexicalDifferenceCalculator.CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void simpleEnumConstantDeclaration() throws IOException {
        EnumConstantDeclaration ecd = considerEcd("A");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(ecd);

        int i = 0;
        assertEquals(new LexicalDifferenceCalculator.CsmChild(ecd.getName()), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    public void csmModelAfterAddingStatementToEmptyBlock() throws IOException {
        LexicalDifferenceCalculator ldc = new LexicalDifferenceCalculator();
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        Statement assignStatement = new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),"aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                ));
        LexicalDifferenceCalculator.CalculatedSyntaxModel calculatedSyntaxModel =
                ldc.calculatedSyntaxModelAfterListAddition(
                        ConcreteSyntaxModel.forClass(BlockStmt.class),
                        ObservableProperty.STATEMENTS,
                        setter.getBody().get().getStatements(),
                        0,
                        assignStatement);
        int index = 0;
        assertEquals(CsmElement.token(GeneratedJavaParserConstants.LBRACE), calculatedSyntaxModel.elements.get(index++));
        assertEquals(CsmElement.newline(), calculatedSyntaxModel.elements.get(index++));
        assertEquals(CsmElement.indent(), calculatedSyntaxModel.elements.get(index++));
        assertTrue(isChild(calculatedSyntaxModel.elements.get(index++), ExpressionStmt.class));
        assertEquals(CsmElement.newline(), calculatedSyntaxModel.elements.get(index++));
        assertEquals(CsmElement.unindent(), calculatedSyntaxModel.elements.get(index++));
        assertEquals(CsmElement.token(GeneratedJavaParserConstants.RBRACE), calculatedSyntaxModel.elements.get(index++));
        assertEquals(index, calculatedSyntaxModel.elements.size());
    }

    @Test
    public void differenceAfterddingStatementToEmptyBlock() throws IOException {
        LexicalDifferenceCalculator ldc = new LexicalDifferenceCalculator();
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        Statement assignStatement = new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),"aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                ));
        Difference diff = ldc.calculateListAdditionDifference(
                ObservableProperty.STATEMENTS,
                setter.getBody().get().getStatements(),
                0,
                assignStatement);
        int index = 0;
        assertEquals(Difference.DifferenceElement.kept(CsmElement.token(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(index++));
        assertEquals(Difference.DifferenceElement.kept(CsmElement.newline()), diff.getElements().get(index++));
        assertEquals(Difference.DifferenceElement.added(CsmElement.indent()), diff.getElements().get(index++));
        assertTrue(isAddedChild(diff.getElements().get(index++), ExpressionStmt.class));
        assertEquals(Difference.DifferenceElement.added(CsmElement.newline()), diff.getElements().get(index++));
        assertEquals(Difference.DifferenceElement.added(CsmElement.unindent()), diff.getElements().get(index++));
        assertEquals(Difference.DifferenceElement.kept(CsmElement.token(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(index++));
        assertEquals(index, diff.getElements().size());
    }

    private boolean isAddedChild(Difference.DifferenceElement element, Class<? extends Node> childClass) {
        return element.isAdded() && isChild(element.getElement(), childClass);
    }

    private boolean isChild(CsmElement element, Class<? extends Node> childClass) {
        return element instanceof LexicalDifferenceCalculator.CsmChild && childClass.isInstance(((LexicalDifferenceCalculator.CsmChild)element).getChild());
    }

    protected EnumConstantDeclaration considerEcd(String code) {
        considerCode("enum A { " + code + " }");
        return ((EnumDeclaration)cu.getType(0)).getEntries().get(0);
    }
}
