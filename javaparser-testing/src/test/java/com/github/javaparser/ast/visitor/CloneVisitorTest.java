package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.visitor.CloneVisitor;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.Iterator;

import static org.junit.Assert.assertEquals;

public class CloneVisitorTest {
    CompilationUnit cu;

    @Before
    public void setUp() {
        cu = new CompilationUnit();
    }

    @After
    public void teardown() {
        cu = null;
    }

    @Test
    public void cloneJavaDocTest() {

        NodeList<BodyDeclaration<?>> bodyDeclarationList = new NodeList<>();
        bodyDeclarationList.add(new AnnotationMemberDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new ConstructorDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new EmptyMemberDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new EnumConstantDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new FieldDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new InitializerDeclaration().setJavaDocComment("javadoc"));
        bodyDeclarationList.add(new MethodDeclaration().setJavaDocComment("javadoc"));

        NodeList<TypeDeclaration<?>> typeDeclarationList = new NodeList<>();
        AnnotationDeclaration annotationDeclaration = new AnnotationDeclaration();
        annotationDeclaration.setName("nnotationDeclarationTest");
        typeDeclarationList.add(annotationDeclaration.setJavaDocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration2 = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration2.setName("emptyTypeDeclarationTest");
        typeDeclarationList.add(classOrInterfaceDeclaration2.setJavaDocComment("javadoc"));

        EnumDeclaration enumDeclaration = new EnumDeclaration();
        enumDeclaration.setName("enumDeclarationTest");
        typeDeclarationList.add(enumDeclaration.setJavaDocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration.setName("classOrInterfaceDeclarationTest");
        typeDeclarationList.add(classOrInterfaceDeclaration.setJavaDocComment("javadoc"));

        ClassOrInterfaceDeclaration classOrInterfaceDeclaration1 = new ClassOrInterfaceDeclaration();
        classOrInterfaceDeclaration1.setName("emptyTypeDeclarationTest1");
        typeDeclarationList.add(classOrInterfaceDeclaration2.setMembers(bodyDeclarationList));

        cu.setTypes(typeDeclarationList);
        CompilationUnit cuClone = (CompilationUnit) new CloneVisitor().visit(cu, null);

        NodeList<TypeDeclaration<?>> typeDeclarationListClone = cuClone.getTypes();
        Iterator<TypeDeclaration<?>> typeItr = typeDeclarationListClone.iterator();
        TypeDeclaration<?> typeDeclaration;
        while (typeItr.hasNext()) {
            typeDeclaration = typeItr.next();
            if (typeDeclaration.getMembers() == null) {
                assertEquals(typeDeclaration.getComment().getContent(), "javadoc");
            } else {
                Iterator<BodyDeclaration<?>> bodyItr = typeDeclaration.getMembers().iterator();
                while (bodyItr.hasNext()) {
                    BodyDeclaration<?> bodyDeclaration = bodyItr.next();
                    assertEquals(bodyDeclaration.getComment().getContent(), "javadoc");
                }
            }
        }

    }

}
