package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

public class Issue232 extends AbstractResolutionTest {
    @Test
    public void issue232() {
        CompilationUnit cu = parseSample("Issue232");
        ClassOrInterfaceDeclaration cls = Navigator.demandClassOrInterface(cu, "OfDouble");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        Context context = JavaParserFactory.getContext(cls, typeSolver);
        SymbolReference<ResolvedTypeDeclaration> reference = context.solveType("OfPrimitive<Double, DoubleConsumer, OfDouble>", typeSolver);
    }
}
