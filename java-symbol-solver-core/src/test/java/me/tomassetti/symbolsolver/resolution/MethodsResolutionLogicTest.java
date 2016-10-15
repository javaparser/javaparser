package me.tomassetti.symbolsolver.resolution;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionFactory;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertEquals;

public class MethodsResolutionLogicTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        File srcNewCode = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new JreTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-generated-sources"))));
        typeSolver = combinedTypeSolverNewCode;
    }

   @Test
   public void compatibilityShouldConsiderAlsoTypeVariablesNegative() {
       JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

       ReferenceType stringType = (ReferenceType) ReflectionFactory.typeUsageFor(String.class, typeSolver);
       ReferenceType rawClassType = (ReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
       ReferenceType classOfStringType = (ReferenceType) rawClassType.replaceParam("T", stringType);
       MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

       assertEquals(false, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(classOfStringType), typeSolver));
   }

    @Test
    public void compatibilityShouldConsiderAlsoTypeVariablesRaw() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ReferenceType rawClassType = (ReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
        MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

        assertEquals(true, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(rawClassType), typeSolver));
    }

    @Test
    public void compatibilityShouldConsiderAlsoTypeVariablesPositive() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ReferenceType runtimeException = (ReferenceType) ReflectionFactory.typeUsageFor(RuntimeException.class, typeSolver);
        ReferenceType rawClassType = (ReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
        ReferenceType classOfRuntimeType = (ReferenceType) rawClassType.replaceParam("T", runtimeException);
        MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

        assertEquals(true, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(classOfRuntimeType), typeSolver));
    }
}
