package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class JavaParserAPIIntegrationTest extends AbstractTest {

    private TypeSolver typeSolver;
    private ResolvedReferenceType string;
    private ResolvedReferenceType listOfBoolean;

    @Before
    public void setup() {
        File src = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(src));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-generated-sources"))));
        typeSolver = combinedTypeSolverNewCode;

        TypeSolver ts = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()), ts);
        ResolvedReferenceType booleanC = new ReferenceTypeImpl(ts.solveType(Boolean.class.getCanonicalName()), ts);
        listOfBoolean = new ReferenceTypeImpl(ts.solveType(List.class.getCanonicalName()), ImmutableList.of(booleanC), ts);
    }

//    @Test
//    public void classDeclarationResolve() throws FileNotFoundException {
//        File f = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
//        CompilationUnit cu = JavaParser.parse(f);
//        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)cu.getType(0);
//        //classOrInterfaceDeclaration.resolve
//    }

    @Test
    public void annotationDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/resources/Annotations.java.txt"));
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(f))).getResult().get();
        AnnotationDeclaration declaration = (AnnotationDeclaration)cu.getType(0);
        assertEquals("MyAnnotation", declaration.getNameAsString());
        ResolvedAnnotationDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    public void constructorDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(f))).getResult().get();
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)cu.getType(0);
        ConstructorDeclaration constructorDeclaration = classOrInterfaceDeclaration.getDefaultConstructor().get();
        ResolvedConstructorDeclaration resolvedConstructorDeclaration = constructorDeclaration.resolve();
    }
}
