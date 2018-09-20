package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistAnnotationDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionAnnotationDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.*;
import static org.mockito.Mockito.mock;

public class AnonymousClassesResolutionTest extends AbstractResolutionTest {

    @BeforeClass
    public static void configureSymbolSolver() throws IOException {
        // configure symbol solver before parsing
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();

        ResolvedReferenceTypeDeclaration cd = mock(ResolvedReferenceTypeDeclaration.class);
        memoryTypeSolver.addDeclaration("org.springframework.transaction.support.TransactionCallbackWithoutResult",
                cd);

        typeSolver.add(memoryTypeSolver);
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @AfterClass
    public static void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        JavaParser.getStaticConfiguration().setSymbolResolver(null);
    }

    // See #1703
    @Test
    public void solveAnonymousClassMethodClass() {
        CompilationUnit cu = parseSample("AnonymousClassMethodClass");

        cu.accept(new VoidVisitorAdapter<Object>() {


            @Override
            public void visit(MethodCallExpr m, Object arg) {
                m.getScope().get().asNameExpr().resolve();
            }
        }, null);

    }


}
