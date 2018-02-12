package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class Issue347 extends AbstractResolutionTest{

    private TypeSolver typeSolver;
    private JavaParserFacade javaParserFacade;

    @Before
    public void setup() {
        typeSolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeSolver);
    }

    @Test
    public void resolvingReferenceToEnumDeclarationInSameFile() {
        String code = "package foo.bar;\nenum Foo {\n" +
                "    FOO_A, FOO_B\n" +
                "}\n" +
                "\n" +
                "class UsingFoo {\n" +
                "    Foo myFooField;\n" +
                "}";
        CompilationUnit cu = JavaParser.parse(code);
        FieldDeclaration fieldDeclaration = Navigator.findNodeOfGivenClass(cu, FieldDeclaration.class);
        ResolvedType fieldType = javaParserFacade.getType(fieldDeclaration);
        assertEquals(true, fieldType.isReferenceType());
        assertEquals(true, fieldType.asReferenceType().getTypeDeclaration().isEnum());
        assertEquals("foo.bar.Foo", fieldType.asReferenceType().getQualifiedName());
    }
}

