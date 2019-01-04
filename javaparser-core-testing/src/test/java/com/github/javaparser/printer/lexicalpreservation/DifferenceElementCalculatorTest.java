package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.concretesyntaxmodel.CsmElement;
import com.github.javaparser.printer.concretesyntaxmodel.CsmIndent;
import com.github.javaparser.printer.concretesyntaxmodel.CsmToken;
import com.github.javaparser.printer.concretesyntaxmodel.CsmUnindent;
import com.github.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.TokenTypes.spaceTokenKind;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static com.github.javaparser.printer.lexicalpreservation.DifferenceElement.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

class DifferenceElementCalculatorTest extends AbstractLexicalPreservingTest {

    @Test
    void calculateDifferenceEmpty() {
        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(a, b);
        assertEquals(0, differenceElements.size());
    }

    @Test
    void calculateDifferenceAIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmToken(GeneratedJavaParserConstants.LPAREN),
                new CsmChild(n1),
                new CsmToken(GeneratedJavaParserConstants.RPAREN),
                new CsmChild(n2)));
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(a, b);
        assertEquals(4, differenceElements.size());
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(0));
        assertEquals(added(new CsmChild(n1)), differenceElements.get(1));
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(2));
        assertEquals(added(new CsmChild(n2)), differenceElements.get(3));
    }

    @Test
    void calculateDifferenceBIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmToken(GeneratedJavaParserConstants.LPAREN),
                new CsmChild(n1),
                new CsmToken(GeneratedJavaParserConstants.RPAREN),
                new CsmChild(n2)));
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(a, b);
        assertEquals(4, differenceElements.size());
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(0));
        assertEquals(removed(new CsmChild(n1)), differenceElements.get(1));
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(2));
        assertEquals(removed(new CsmChild(n2)), differenceElements.get(3));
    }

    @Test
    void compilationUnitExampleWithPackageSetDiff() {
        considerCode("class A {}");
        CsmElement element = ConcreteSyntaxModel.forClass(cu.getClass());
        PackageDeclaration packageDeclaration = new PackageDeclaration(new Name(new Name("foo"), "bar"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, cu);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, cu, ObservableProperty.PACKAGE_DECLARATION, null, packageDeclaration);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        assertEquals(3, differenceElements.size());
        assertEquals(added(new CsmChild(packageDeclaration)), differenceElements.get(0));
        assertEquals(kept(new CsmChild(cu.getType(0))), differenceElements.get(1));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(2));
    }

    @Test
    void annotationDeclarationExampleWithModifierAdded() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, new NodeList<>(), createModifierList(PUBLIC));
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        DifferenceElementCalculator.removeIndentationElements(differenceElements);
        int i = 0;
        assertEquals(added(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void annotationDeclarationExampleWithNameChanged() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        SimpleName newName = new SimpleName("NewName");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.NAME,
                annotationDeclaration.getName(), newName);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        DifferenceElementCalculator.removeIndentationElements(differenceElements);
        int i = 0;
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(removed(new CsmChild(annotationDeclaration.getName())), differenceElements.get(i++));
        assertEquals(added(new CsmChild(newName)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void annotationDeclarationExampleWithJavadocAdded() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        JavadocComment comment = new JavadocComment("Cool this annotation!");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, null, comment);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        DifferenceElementCalculator.removeIndentationElements(differenceElements);
        int i = 0;
        assertEquals(kept(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void annotationDeclarationExampleWithJavadocRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example9_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, annotationDeclaration.getComment().get(), null);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        DifferenceElementCalculator.removeIndentationElements(differenceElements);
        int i = 0;
        assertEquals(kept(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void annotationDeclarationExampleWithModifierRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, createModifierList(PUBLIC), new NodeList<>());
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        DifferenceElementCalculator.removeIndentationElements(differenceElements);
        int i = 0;
        assertEquals(removed(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void removeDefaultValueInAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration md = considerAmd("int foo() default 10;");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(md, ObservableProperty.DEFAULT_VALUE, md.getDefaultValue(), null);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(kept(new CsmChild(md.getType())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(md.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants._DEFAULT)), differenceElements.get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(removed(new CsmChild(md.getDefaultValue().get())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.SEMICOLON)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void addedDefaultValueInAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration md = considerAmd("int foo();");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        Expression defaultValue = new IntegerLiteralExpr(("10"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(md, ObservableProperty.DEFAULT_VALUE, null, defaultValue);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(kept(new CsmChild(md.getType())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(md.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants._DEFAULT)), differenceElements.get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(added(new CsmChild(defaultValue)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.SEMICOLON)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void addedModifierToConstructorDeclaration() {
        ConstructorDeclaration cd = considerCd("A(){}");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(cd);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(cd, ObservableProperty.MODIFIERS,
                new NodeList<>(), createModifierList(PUBLIC));
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(added(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(cd.getName())), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(kept(new CsmChild(cd.getBody())), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void replacingNameForEnumConstantDeclaration() {
        EnumConstantDeclaration ecd = considerEcd("A");
        SimpleName newName = new SimpleName("B");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(ecd);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(ecd, ObservableProperty.NAME,
                ecd.getName(), newName);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(DifferenceElement.removed(new CsmChild(ecd.getName())), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmChild(newName)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void addingStatementToEmptyMethodBody() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS
        ));
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(m.getBody().get());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListAddition(m.getBody().get(), ObservableProperty.STATEMENTS, 0, s);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmIndent()), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmChild(s)), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmToken(eolTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmUnindent()), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void methodDeclarationRemovingParameter() {
        MethodDeclaration md = considerMd("public void foo(float f){}");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListRemoval(md, ObservableProperty.PARAMETERS, 0);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(DifferenceElement.kept(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getType())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getName())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(i++));
        assertEquals(DifferenceElement.removed(new CsmChild(md.getParameter(0))), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getBody().get())), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    @Test
    void methodDeclarationAddingParameter() {
        MethodDeclaration md = considerMd("public void foo(){}");
        Parameter newParameter = new Parameter(new ArrayType(PrimitiveType.intType()), new SimpleName("foo"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListAddition(md, ObservableProperty.PARAMETERS, 0, newParameter);
        List<DifferenceElement> differenceElements = DifferenceElementCalculator.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(DifferenceElement.kept(new CsmChild(Modifier.publicModifier())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getType())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getName())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), differenceElements.get(i++));
        assertEquals(DifferenceElement.added(new CsmChild(newParameter)), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmToken(spaceTokenKind())), differenceElements.get(i++));
        assertEquals(DifferenceElement.kept(new CsmChild(md.getBody().get())), differenceElements.get(i++));
        assertEquals(i, differenceElements.size());
    }

    private AnnotationMemberDeclaration considerAmd(String code) {
        considerCode("@interface AD { " + code + " }");
        return (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("AD").get().getMember(0);
    }

    private ConstructorDeclaration considerCd(String code) {
        considerCode("class A { " + code + " }");
        return (ConstructorDeclaration) cu.getType(0).getMembers().get(0);
    }

    private EnumConstantDeclaration considerEcd(String code) {
        considerCode("enum A { " + code + " }");
        return ((EnumDeclaration)cu.getType(0)).getEntries().get(0);
    }

    private MethodDeclaration considerMd(String code) {
        considerCode("class A { " + code + " }");
        return (MethodDeclaration) cu.getType(0).getMembers().get(0);
    }
}
