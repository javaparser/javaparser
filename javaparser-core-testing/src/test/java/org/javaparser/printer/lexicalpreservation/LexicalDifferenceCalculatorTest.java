/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package org.javaparser.printer.lexicalpreservation;

import org.javaparser.GeneratedJavaParserConstants;
import org.javaparser.ast.Modifier;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.PackageDeclaration;
import org.javaparser.ast.body.AnnotationDeclaration;
import org.javaparser.ast.body.EnumConstantDeclaration;
import org.javaparser.ast.body.EnumDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.comments.JavadocComment;
import org.javaparser.ast.expr.*;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.stmt.BlockStmt;
import org.javaparser.ast.stmt.ExpressionStmt;
import org.javaparser.ast.stmt.Statement;
import org.javaparser.printer.ConcreteSyntaxModel;
import org.javaparser.printer.concretesyntaxmodel.CsmElement;
import org.javaparser.printer.concretesyntaxmodel.CsmToken;
import org.javaparser.printer.lexicalpreservation.LexicalDifferenceCalculator.CsmChild;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;

import static org.javaparser.TokenTypes.eolTokenKind;
import static org.javaparser.TokenTypes.spaceTokenKind;
import static org.javaparser.ast.Modifier.Keyword.PUBLIC;
import static org.javaparser.ast.Modifier.createModifierList;
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
