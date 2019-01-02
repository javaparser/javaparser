package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class AnonymousClassesResolutionTest extends AbstractResolutionTest {

    @BeforeAll
    static void configureSymbolSolver() throws IOException {
        // configure symbol solver before parsing
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();

        ResolvedReferenceTypeDeclaration cd = mock(ResolvedReferenceTypeDeclaration.class);
        when(cd.asReferenceType()).thenReturn(cd);
        memoryTypeSolver.addDeclaration("org.springframework.transaction.support.TransactionCallbackWithoutResult",
                cd);

        typeSolver.add(memoryTypeSolver);
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @AfterAll
    static void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        JavaParser.getStaticConfiguration().setSymbolResolver(null);
    }

    // See #1703
    @Test
    void solveAnonymousClassMethodClass() {
        CompilationUnit cu = parseSample("AnonymousClassMethodClass");

        cu.accept(new VoidVisitorAdapter<Object>() {


            @Override
            public void visit(MethodCallExpr m, Object arg) {
                m.getScope().get().asNameExpr().resolve();
            }
        }, null);

    }


}
