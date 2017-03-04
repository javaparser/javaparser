package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import org.junit.Test;

import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * See issue #16
 */
public class DefaultPackageTest {

    private class MyClassDeclaration extends AbstractClassDeclaration {

        private String qualifiedName;

        private MyClassDeclaration(String qualifiedName) {
            this.qualifiedName = qualifiedName;
        }

        @Override
        public AccessLevel accessLevel() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<TypeParameterDeclaration> getTypeParameters() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getName() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ReferenceType> getAncestors() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<FieldDeclaration> getAllFields() {
            throw new UnsupportedOperationException();
        }

        @Override
        public Set<MethodDeclaration> getDeclaredMethods() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean isAssignableBy(Type type) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean isAssignableBy(ReferenceTypeDeclaration other) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean hasDirectlyAnnotation(String qualifiedName) {
            throw new UnsupportedOperationException();
        }

        @Override
        public ReferenceType getSuperClass() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ReferenceType> getInterfaces() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ConstructorDeclaration> getConstructors() {
            throw new UnsupportedOperationException();
        }

        @Override
        protected ReferenceType object() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getQualifiedName() {
            return qualifiedName;
        }
    }

    @Test
    public void aClassInDefaultPackageCanBeAccessedFromTheDefaultPackage() {
        String code = "class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));

        ClassOrInterfaceType jpType = JavaParser.parse(code).getClassByName("A").get().getExtendedTypes(0);
        Type resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(jpType);
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    }

    @Test(expected = UnsolvedSymbolException.class)
    public void aClassInDefaultPackageCanBeAccessedFromOutsideTheDefaultPackageImportingIt() {
        String code = "package myPackage; import B; class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));

        ClassOrInterfaceType jpType = JavaParser.parse(code).getClassByName("A").get().getExtendedTypes(0);
        Type resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(jpType);
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    }

    @Test(expected = UnsolvedSymbolException.class)
    public void aClassInDefaultPackageCanBeAccessedFromOutsideTheDefaultPackageWithoutImportingIt() {
        String code = "package myPackage; class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));

        Type resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(JavaParser.parse(code).getClassByName("A").get().getExtendedTypes(0));
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    }
}
