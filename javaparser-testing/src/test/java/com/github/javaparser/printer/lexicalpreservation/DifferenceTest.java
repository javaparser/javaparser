package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
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
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;

import static com.github.javaparser.TokenTypes.eolTokenKind;
import static com.github.javaparser.TokenTypes.spaceTokenKind;
import static com.github.javaparser.printer.lexicalpreservation.Difference.DifferenceElement.*;
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
                new CsmToken(GeneratedJavaParserConstants.LPAREN),
                new CsmChild(n1),
                new CsmToken(GeneratedJavaParserConstants.RPAREN),
                new CsmChild(n2)));
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(added(new CsmChild(n1)), diff.getElements().get(1));
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(2));
        assertEquals(added(new CsmChild(n2)), diff.getElements().get(3));
    }

    @Test
    public void calculateDifferenceBIsEmpty() {
        Node n1 = new FieldDeclaration();
        Node n2 = new MethodDeclaration();

        LexicalDifferenceCalculator.CalculatedSyntaxModel a = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Arrays.asList(
                new CsmToken(GeneratedJavaParserConstants.LPAREN),
                new CsmChild(n1),
                new CsmToken(GeneratedJavaParserConstants.RPAREN),
                new CsmChild(n2)));
        LexicalDifferenceCalculator.CalculatedSyntaxModel b = new LexicalDifferenceCalculator.CalculatedSyntaxModel(Collections.emptyList());
        Difference diff = Difference.calculate(a, b);
        assertEquals(4, diff.getElements().size());
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(0));
        assertEquals(removed(new CsmChild(n1)), diff.getElements().get(1));
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(2));
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
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(2));
    }

    @Test
    public void annotationDeclarationExampleWithModifierAdded() throws IOException {
        considerExample("AnnotationDeclaration_Example1_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, EnumSet.noneOf(Modifier.class), EnumSet.of(Modifier.PUBLIC));
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        diff.removeIndentationElements();
        int i = 0;
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
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
        diff.removeIndentationElements();
        int i = 0;
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(removed(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(added(new CsmChild(newName)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
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
        diff.removeIndentationElements();
        int i = 0;
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void annotationDeclarationExampleWithJavadocRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example9_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.COMMENT, annotationDeclaration.getComment().get(), null);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        diff.removeIndentationElements();
        int i = 0;
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void annotationDeclarationExampleWithModifierRemoved() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        AnnotationDeclaration annotationDeclaration = (AnnotationDeclaration)cu.getType(0);
        CsmElement element = ConcreteSyntaxModel.forClass(annotationDeclaration.getClass());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(element, annotationDeclaration);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(element, annotationDeclaration, ObservableProperty.MODIFIERS, EnumSet.of(Modifier.PUBLIC), EnumSet.noneOf(Modifier.class));
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        diff.removeIndentationElements();
        int i = 0;
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.AT)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.INTERFACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(0))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(1))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(2))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(3))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(4))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(annotationDeclaration.getMember(5))), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void removeDefaultValueInAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration md = considerAmd("int foo() default 10;");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(md, ObservableProperty.DEFAULT_VALUE, md.getDefaultValue(), null);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(kept(new CsmChild(md.getType())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(md.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(GeneratedJavaParserConstants._DEFAULT)), diff.getElements().get(i++));
        assertEquals(removed(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(removed(new CsmChild(md.getDefaultValue().get())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.SEMICOLON)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void addedDefaultValueInAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration md = considerAmd("int foo();");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        Expression defaultValue = new IntegerLiteralExpr(("10"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(md, ObservableProperty.DEFAULT_VALUE, null, defaultValue);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(kept(new CsmChild(md.getType())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(md.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants._DEFAULT)), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(added(new CsmChild(defaultValue)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.SEMICOLON)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void addedModifierToConstructorDeclaration() {
        ConstructorDeclaration cd = considerCd("A(){}");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(cd);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(cd, ObservableProperty.MODIFIERS,
                EnumSet.noneOf(Modifier.class), EnumSet.of(Modifier.PUBLIC));
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(added(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(added(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(cd.getName())), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(kept(new CsmChild(cd.getBody())), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void replacingNameForEnumConstantDeclaration() throws IOException {
        EnumConstantDeclaration ecd = considerEcd("A");
        SimpleName newName = new SimpleName("B");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(ecd);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterPropertyChange(ecd, ObservableProperty.NAME,
                ecd.getName(), newName);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(Difference.DifferenceElement.removed(new CsmChild(ecd.getName())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmChild(newName)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void addingStatementToEmptyMethodBody() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS
        ));
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(m.getBody().get());
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListAddition(m.getBody().get(), ObservableProperty.STATEMENTS, 0, s);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LBRACE)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmIndent()), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmChild(s)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmToken(eolTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmUnindent()), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RBRACE)), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void methodDeclarationRemovingParameter() {
        MethodDeclaration md = considerMd("public void foo(float f){}");
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListRemoval(md, ObservableProperty.PARAMETERS, 0);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getType())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getName())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.removed(new CsmChild(md.getParameter(0))), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getBody().get())), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
    }

    @Test
    public void methodDeclarationAddingParameter() {
        MethodDeclaration md = considerMd("public void foo(){}");
        Parameter newParameter = new Parameter(new ArrayType(PrimitiveType.intType()), new SimpleName("foo"));
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmOriginal = new LexicalDifferenceCalculator().calculatedSyntaxModelForNode(md);
        LexicalDifferenceCalculator.CalculatedSyntaxModel csmChanged = new LexicalDifferenceCalculator().calculatedSyntaxModelAfterListAddition(md, ObservableProperty.PARAMETERS, 0, newParameter);
        Difference diff = Difference.calculate(csmOriginal, csmChanged);
        int i = 0;
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.PUBLIC)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getType())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getName())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.LPAREN)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.added(new CsmChild(newParameter)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(GeneratedJavaParserConstants.RPAREN)), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmToken(spaceTokenKind())), diff.getElements().get(i++));
        assertEquals(Difference.DifferenceElement.kept(new CsmChild(md.getBody().get())), diff.getElements().get(i++));
        assertEquals(i, diff.getElements().size());
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
