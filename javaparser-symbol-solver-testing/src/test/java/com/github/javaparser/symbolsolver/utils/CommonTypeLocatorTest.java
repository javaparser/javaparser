package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

class CommonTypeLocatorTest {
    private final CommonTypeLocator locator = new CommonTypeLocator();

    @Test
    void oneObjectReturnsItself() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedReferenceType function = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Function.class, typeSolver), typeSolver);
        ResolvedReferenceType commonAncestor = locator.findCommonType(Collections.singletonList(function)).get();
        assertEquals("java.util.Function", commonAncestor.getQualifiedName());
    }

    @Test
    void oneObjectThatImplementsTheSecondsObjectReturnsTheFirstObject() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedReferenceType list = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeSolver), typeSolver);
        ResolvedReferenceType arrayList = new ReferenceTypeImpl(new ReflectionClassDeclaration(ArrayList.class, typeSolver), typeSolver);
        ResolvedReferenceType commonAncestor = locator.findCommonType(Arrays.asList(list, arrayList)).get();


        System.out.println(arrayList.getDirectClassAncestor());
        List<ResolvedReferenceType> directAncestors = arrayList.getDirectAncestors();
        System.out.println(directAncestors.stream().map(anc -> anc.toString()).collect(Collectors.joining("\n")));

        List<ResolvedReferenceType> allAncestors = arrayList.getAllAncestors();
        System.out.println(allAncestors.stream().map(anc -> anc.toString()).collect(Collectors.joining("\n")));

        assertEquals("java.util.List", commonAncestor.getQualifiedName());
    }

}