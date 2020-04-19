package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.*;

public class Issue2602Test extends AbstractSymbolResolutionTest {

    private JavaParser javaParser;
    private CompilationUnit cu;
    private MemoryTypeSolver typeSolver;
    private ParserConfiguration configuration;


    @BeforeEach
    public void setUp() {
        typeSolver = new MemoryTypeSolver();
        configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        javaParser = new JavaParser(configuration);

        //language=JAVA
        String src = "package java.lang;" +
                " class Object {}\n" +
                "\n" +
                "class A extends Object {}\n" +
                "\n" +
                "class B extends Object {}\n";


        ParseResult<CompilationUnit> parseResult = javaParser.parse(
                ParseStart.COMPILATION_UNIT,
                provider(src)
        );


        System.out.println("parseResult = " + parseResult);
        parseResult.getProblems().forEach(problem -> System.out.println("problem.getVerboseMessage() = " + problem.getVerboseMessage()));

        assertTrue(parseResult.isSuccessful());
        assertEquals(0, parseResult.getProblems().size(), "Expected zero errors when attempting to parse the input code.");
        assertTrue(parseResult.getResult().isPresent(), "Must have a parse result to run this test.");

        this.cu = parseResult.getResult().get();

        JavaParserFacade javaParserFacade = JavaParserFacade.get(this.typeSolver);

        for (TypeDeclaration t : this.cu.getTypes()) {
            JavaParserClassDeclaration classDecl = new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) t, this.typeSolver);

            this.typeSolver.addDeclaration((String) t.getFullyQualifiedName().get(), classDecl);
        }
    }


    @Test
    public void doTest_checkForRecursionWhen_java_lang_Object_IsA_JavaParserClassDeclaration() {

        ResolvedReferenceTypeDeclaration thisDeclaration = typeSolver.solveType("java.lang.A");
        ResolvedReferenceTypeDeclaration secondDeclaration = typeSolver.solveType("java.lang.B");

        assertFalse(thisDeclaration.canBeAssignedTo(secondDeclaration), "Both types should not be assignable");
    }


}
