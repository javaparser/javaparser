package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
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
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class JavaParserAPIIntegrationTest extends AbstractTest {

    private TypeSolver typeSolver;
    private ResolvedReferenceType string;
    private ResolvedReferenceType listOfBoolean;

    @Before
    public void setup() {
        File src = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(src));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"))));
        typeSolver = combinedTypeSolverNewCode;

        TypeSolver ts = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()), ts);
        ResolvedReferenceType booleanC = new ReferenceTypeImpl(ts.solveType(Boolean.class.getCanonicalName()), ts);
        listOfBoolean = new ReferenceTypeImpl(ts.solveType(List.class.getCanonicalName()), ImmutableList.of(booleanC), ts);
    }

    @Test
    public void annotationDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/resources/Annotations.java.txt"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        AnnotationDeclaration declaration = (AnnotationDeclaration)cu.getType(0);
        assertEquals("MyAnnotation", declaration.getNameAsString());
        ResolvedAnnotationDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    public void annotationMemberDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/resources/Annotations.java.txt"));
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(f))).getResult().get();
        AnnotationDeclaration declaration = (AnnotationDeclaration)cu.getType(2);
        assertEquals("MyAnnotationWithFields", declaration.getNameAsString());
        AnnotationMemberDeclaration memberDeclaration = (AnnotationMemberDeclaration)declaration.getMember(0);
        ResolvedAnnotationMemberDeclaration resolvedDeclaration = memberDeclaration.resolve();
    }

    @Test
    public void classDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration declaration = (ClassOrInterfaceDeclaration)cu.getType(0);
        declaration.resolve();
    }

    @Test
    public void interfaceDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/resources/MethodTypeParams.java.txt"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration declaration = (ClassOrInterfaceDeclaration)cu.getType(1);
        assertEquals("VoidVisitor", declaration.getNameAsString());
        assertEquals(true, declaration.isInterface());
        declaration.resolve();
    }

    private CompilationUnit parseWithSymbolResolution(File f) throws IOException {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        return new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(f))).getResult().get();
    }

    @Test
    public void constructorDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)cu.getType(0);
        ConstructorDeclaration constructorDeclaration = classOrInterfaceDeclaration.getDefaultConstructor().get();
        ResolvedConstructorDeclaration resolvedConstructorDeclaration = constructorDeclaration.resolve();
    }
    @Test
    public void enumDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/AccessSpecifier.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        EnumDeclaration declaration = (EnumDeclaration) cu.getType(0);
        assertEquals("AccessSpecifier", declaration.getNameAsString());
        ResolvedEnumDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    public void enumConstantDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/AccessSpecifier.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        EnumDeclaration enumDeclaration = (EnumDeclaration) cu.getType(0);
        assertEquals("AccessSpecifier", enumDeclaration.getNameAsString());
        EnumConstantDeclaration declaration = enumDeclaration.getEntry(0);
        assertEquals("PUBLIC", declaration.getNameAsString());
        ResolvedEnumConstantDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    public void fieldDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        FieldDeclaration declaration = classDeclaration.getFields().get(0);
        ResolvedFieldDeclaration resolvedDeclaration = declaration.resolve();
    }

    // TODO make VariableDeclarator resolvable

    @Test
    public void methodDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        MethodDeclaration declaration = classDeclaration.getMethodsByName("getComments").get(0);
        ResolvedMethodDeclaration resolvedDeclaration = declaration.resolve();
        assertEquals("getComments", resolvedDeclaration.getName());
        assertEquals(0, resolvedDeclaration.getNumberOfParams());
    }

    @Test
    public void parameterDeclarationResolve() throws IOException {
        File f = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java"));
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StreamProvider(new FileInputStream(f))).getResult().get();
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        MethodDeclaration methodDeclaration = classDeclaration.getMethodsByName("setComments").get(0);
        Parameter declaration = methodDeclaration.getParameter(0);
        ResolvedParameterDeclaration resolvedDeclaration = declaration.resolve();
    }

}
