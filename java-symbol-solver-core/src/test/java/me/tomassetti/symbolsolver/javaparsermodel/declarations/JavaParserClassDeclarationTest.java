package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.google.common.collect.ImmutableSet;
import me.tomassetti.symbolsolver.AbstractTest;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class JavaParserClassDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver;
    private TypeSolver typeSolverNewCode;

    @Before
    public void setup() {
        File src = adaptPath(new File("src/test/resources/javaparser_src/proper_source"));
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_src/generated"))));
        typeSolver = combinedTypeSolver;

        File srcNewCode = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new JreTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-generated-sources"))));
        typeSolverNewCode = combinedTypeSolverNewCode;
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isClass());
    }

    @Test
    public void testIsInterface() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isInterface());
    }

    @Test
    public void testIsEnum() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isTypeVariable());
    }

    @Test
    public void testIsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isType());
    }

    @Test
    public void testAsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    public void testAsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asClass());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asInterface();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsEnum() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asEnum();
    }

    @Test
    public void testGetQualifiedName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.CompilationUnit", compilationUnit.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    public void testGetSuperclassWithoutTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    }

    @Test
    public void testGetSuperclassWithTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", compilationUnit.getSuperClass().getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllSuperclassesWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllSuperclassesWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(3, constructorDeclaration.getAllSuperClasses().size());

        me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAllSuperClasses().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
    }

    @Test
    public void testGetInterfacesWithoutParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"), coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(7, constructorDeclaration.getInterfaces().size());

        me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType interfaze = null;

        interfaze = constructorDeclaration.getInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllInterfacesWithoutParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable"), compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.NamedNode", "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAllInterfaces().size());

        me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType interfaze = null;

        interfaze = constructorDeclaration.getAllInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(7);
        assertEquals("java.lang.Cloneable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(8, constructorDeclaration.getAncestors().size());

        me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllAncestorsWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(12, constructorDeclaration.getAllAncestors().size());

        me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAllAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(2);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(4);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(9);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(10);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(11);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }
}
