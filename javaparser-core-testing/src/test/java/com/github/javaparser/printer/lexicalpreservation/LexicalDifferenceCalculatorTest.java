package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
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
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.TokenTypes.spaceTokenKind;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class LexicalDifferenceCalculatorTest extends AbstractLexicalPreservingTest {

    @Test
    void compilationUnitExampleOriginal() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, cu);
        assertEquals(2, csmOriginal.elements.size());
        assertEquals(new CsmChild(cu.getType(0)), csmOriginal.elements.get(0));
        assertEquals(new CsmToken(eolTokenKind()), csmOriginal.elements.get(1));
    }

    @Test
    void compilationUnitExampleWithPackageSet() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        PackageDeclaration packageDeclaration = new PackageDeclaration(new Name(new Name("foo"), "bar"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, cu, ObservableProperty.PACKAGE_DECLARATION, null, packageDeclaration);
        assertEquals(3, csmChanged.elements.size());
        assertEquals(new CsmChild(packageDeclaration), csmChanged.elements.get(0));
        assertEquals(new CsmChild(cu.getType(0)), csmChanged.elements.get(1));
        assertEquals(new CsmToken(eolTokenKind()), csmChanged.elements.get(2));
    }

    @Test
    void annotationDeclarationModifiersExampleOriginal() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void annotationDeclarationModifiersExampleModified() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, new NodeList<>(), createModifierList(PUBLIC));
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmChild(Modifier.publicModifier()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void annotationDeclarationNameExampleModified() throws IOException {
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
        assertEquals(new CsmChild(newName), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void annotationDeclarationJavadocExampleOriginal() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmChild(Modifier.publicModifier()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void annotationDeclarationJavadocExampleAddingJavadoc() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        JavadocComment comment = new JavadocComment("Cool this annotation!");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, null, comment);
        csm.removeIndentationElements();
        int i = 0;
        assertEquals(new CsmChild(Modifier.publicModifier()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.AT), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.INTERFACE), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getName()), csm.elements.get(i++));
        assertEquals(new CsmToken(spaceTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.LBRACE), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(0)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(1)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(2)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(3)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(4)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmChild(annotationDeclaration.getMember(5)), csm.elements.get(i++));
        assertEquals(new CsmToken(eolTokenKind()), csm.elements.get(i++));
        assertEquals(new CsmToken(GeneratedJavaParserConstants.RBRACE), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void simpleEnumConstantDeclaration() {
        EnumConstantDeclaration ecd = considerEcd("A");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csm = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(ecd);

        int i = 0;
        assertEquals(new CsmChild(ecd.getName()), csm.elements.get(i++));
        assertEquals(i, csm.elements.size());
    }

    @Test
    void csmModelAfterAddingStatementToEmptyBlock() throws IOException {
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
    void differenceAfterddingStatementToEmptyBlock() throws IOException {
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
        List<DifferenceElement> differenceElements = ldc.calculateListAdditionDifference(
                ObservableProperty.STATEMENTS,
                setter.getBody().get().getStatements(),
                0,
                assignStatement);
        int index = 0;
        assertEquals(DifferenceElement.kept(CsmElement.token(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(index++));
        assertEquals(DifferenceElement.kept(CsmElement.newline()), differenceElements.get(index++));
        assertEquals(DifferenceElement.added(CsmElement.indent()), differenceElements.get(index++));
        assertTrue(isAddedChild(differenceElements.get(index++), ExpressionStmt.class));
        assertEquals(DifferenceElement.added(CsmElement.newline()), differenceElements.get(index++));
        assertEquals(DifferenceElement.added(CsmElement.unindent()), differenceElements.get(index++));
        assertEquals(DifferenceElement.kept(CsmElement.token(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(index++));
        assertEquals(index, differenceElements.size());
    }

    private boolean isAddedChild(DifferenceElement element, Class<? extends Node> childClass) {
        return element.isAdded() && isChild(element.getElement(), childClass);
    }

    private boolean isChild(CsmElement element, Class<? extends Node> childClass) {
        return element instanceof CsmChild && childClass.isInstance(((CsmChild)element).getChild());
    }

    protected EnumConstantDeclaration considerEcd(String code) {
        considerCode("enum A { " + code + " }");
        return ((EnumDeclaration)cu.getType(0)).getEntries().get(0);
    }
}
