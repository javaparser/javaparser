package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;

class JavaParserAPIIntegrationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;
    private ResolvedReferenceType string;
    private ResolvedReferenceType listOfBoolean;

    @BeforeEach
    void setup() {
        Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"), new LeanParserConfiguration()));
        typeSolver = combinedTypeSolverNewCode;

        TypeSolver ts = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()), ts);
        ResolvedReferenceType booleanC = new ReferenceTypeImpl(ts.solveType(Boolean.class.getCanonicalName()), ts);
        listOfBoolean = new ReferenceTypeImpl(ts.solveType(List.class.getCanonicalName()), ImmutableList.of(booleanC), ts);
    }

    @Test
    void annotationDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/resources/Annotations.java.txt");
        CompilationUnit cu = parseWithSymbolResolution(f);
        AnnotationDeclaration declaration = (AnnotationDeclaration)cu.getType(0);
        assertEquals("MyAnnotation", declaration.getNameAsString());
        ResolvedAnnotationDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    void annotationMemberDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/resources/Annotations.java.txt");
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, provider(f)).getResult().get();
        AnnotationDeclaration declaration = (AnnotationDeclaration)cu.getType(3);
        assertEquals("MyAnnotationWithElements", declaration.getNameAsString());
        AnnotationMemberDeclaration memberDeclaration = (AnnotationMemberDeclaration)declaration.getMember(0);
        ResolvedAnnotationMemberDeclaration resolvedDeclaration = memberDeclaration.resolve();
    }

    @Test
    void classDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration declaration = (ClassOrInterfaceDeclaration)cu.getType(0);
        declaration.resolve();
    }

    @Test
    void interfaceDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/resources/MethodTypeParams.java.txt");
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration declaration = (ClassOrInterfaceDeclaration)cu.getType(1);
        assertEquals("VoidVisitor", declaration.getNameAsString());
        assertEquals(true, declaration.isInterface());
        declaration.resolve();
    }

    private CompilationUnit parseWithSymbolResolution(Path f) throws IOException {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        return new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, provider(f)).getResult().get();
    }

    @Test
    void constructorDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)cu.getType(0);
        ConstructorDeclaration constructorDeclaration = classOrInterfaceDeclaration.getDefaultConstructor().get();
        ResolvedConstructorDeclaration resolvedConstructorDeclaration = constructorDeclaration.resolve();
    }
    @Test
    void enumDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/AccessSpecifier.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        EnumDeclaration declaration = (EnumDeclaration) cu.getType(0);
        assertEquals("AccessSpecifier", declaration.getNameAsString());
        ResolvedEnumDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    void enumConstantDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/AccessSpecifier.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        EnumDeclaration enumDeclaration = (EnumDeclaration) cu.getType(0);
        assertEquals("AccessSpecifier", enumDeclaration.getNameAsString());
        EnumConstantDeclaration declaration = enumDeclaration.getEntry(0);
        assertEquals("PUBLIC", declaration.getNameAsString());
        ResolvedEnumConstantDeclaration resolvedDeclaration = declaration.resolve();
    }

    @Test
    void fieldDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        FieldDeclaration declaration = classDeclaration.getFields().get(0);
        ResolvedFieldDeclaration resolvedDeclaration = declaration.resolve();
    }

    // TODO make VariableDeclarator resolvable

    @Test
    void methodDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java");
        CompilationUnit cu = parseWithSymbolResolution(f);
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        MethodDeclaration declaration = classDeclaration.getMethodsByName("getComments").get(0);
        ResolvedMethodDeclaration resolvedDeclaration = declaration.resolve();
        assertEquals("getComments", resolvedDeclaration.getName());
        assertEquals(0, resolvedDeclaration.getNumberOfParams());
    }

    @Test
    void parameterDeclarationResolve() throws IOException {
        Path f = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core/com/github/javaparser/ast/CompilationUnit.java");
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, provider(f)).getResult().get();
        ClassOrInterfaceDeclaration classDeclaration = (ClassOrInterfaceDeclaration) cu.getType(0);
        assertEquals("CompilationUnit", classDeclaration.getNameAsString());
        MethodDeclaration methodDeclaration = classDeclaration.getMethodsByName("setComments").get(0);
        Parameter declaration = methodDeclaration.getParameter(0);
        ResolvedParameterDeclaration resolvedDeclaration = declaration.resolve();
    }

}
