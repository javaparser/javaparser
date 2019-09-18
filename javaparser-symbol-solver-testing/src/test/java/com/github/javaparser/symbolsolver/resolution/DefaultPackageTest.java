package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * See issue #16
 */
class DefaultPackageTest {

    private class MyClassDeclaration extends AbstractClassDeclaration {

        private String qualifiedName;

        private MyClassDeclaration(String qualifiedName) {
            this.qualifiedName = qualifiedName;
        }

        @Override
        public AccessSpecifier accessSpecifier() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
            return new LinkedList<>();
        }

        @Override
        public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
            return new HashSet<>();
        }

        @Override
        public String getName() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ResolvedFieldDeclaration> getAllFields() {
            throw new UnsupportedOperationException();
        }

        @Override
        public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean isAssignableBy(ResolvedType type) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean hasDirectlyAnnotation(String qualifiedName) {
            throw new UnsupportedOperationException();
        }

        @Override
        public ResolvedReferenceType getSuperClass() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ResolvedReferenceType> getInterfaces() {
            throw new UnsupportedOperationException();
        }

        @Override
        public List<ResolvedConstructorDeclaration> getConstructors() {
            throw new UnsupportedOperationException();
        }

        @Override
        protected ResolvedReferenceType object() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getPackageName() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getClassName() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String getQualifiedName() {
            return qualifiedName;
        }

        @Override
        public Optional<ResolvedReferenceTypeDeclaration> containerType() {
            throw new UnsupportedOperationException();
        }

        @Override
        public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
            throw new UnsupportedOperationException();
        }
    }

    @Test
    void aClassInDefaultPackageCanBeAccessedFromTheDefaultPackage() {
        String code = "class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));

        ClassOrInterfaceType jpType = parse(code).getClassByName("A").get().getExtendedTypes(0);
        ResolvedType resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(jpType);
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    }

    @Test
    void aClassInDefaultPackageCanBeAccessedFromOutsideTheDefaultPackageImportingIt() {
        assertThrows(UnsolvedSymbolException.class, () -> {
            String code = "package myPackage; import B; class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));
        ClassOrInterfaceType jpType = parse(code).getClassByName("A").get().getExtendedTypes(0);
        ResolvedType resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(jpType);
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    });
                
                }

    @Test
    void aClassInDefaultPackageCanBeAccessedFromOutsideTheDefaultPackageWithoutImportingIt() {
        assertThrows(UnsolvedSymbolException.class, () -> {
            String code = "package myPackage; class A extends B {}";
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
        memoryTypeSolver.addDeclaration("B", new MyClassDeclaration("B"));
        ResolvedType resolvedType = JavaParserFacade.get(memoryTypeSolver).convertToUsage(parse(code).getClassByName("A").get().getExtendedTypes(0));
        assertEquals("B", resolvedType.asReferenceType().getQualifiedName());
    });
                
        }
}
