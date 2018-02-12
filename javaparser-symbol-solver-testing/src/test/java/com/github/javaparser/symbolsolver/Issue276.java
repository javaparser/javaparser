package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

public class Issue276 extends AbstractResolutionTest{

    @Test
    public void testSolveStaticallyImportedMemberType() throws FileNotFoundException {
        CompilationUnit cu = JavaParser.parse(new File(adaptPath("src/test/resources/issue276/foo/C.java")));
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "C");
        TypeSolver typeSolver = new CombinedTypeSolver(
        		new ReflectionTypeSolver(), 
        		new JavaParserTypeSolver(adaptPath(new File("src/test/resources/issue276"))));
        List<MethodDeclaration> methods = cls.findAll(MethodDeclaration.class);
        boolean isSolved = false;
        for (MethodDeclaration method: methods) {
        	if (method.getNameAsString().equals("overrideMe")) {
        		MethodContext context = new MethodContext(method, typeSolver);
        		isSolved = context.solveType("FindMeIfYouCan", typeSolver).isSolved();
        	}
        }
        Assert.assertTrue(isSolved);
    }
}
