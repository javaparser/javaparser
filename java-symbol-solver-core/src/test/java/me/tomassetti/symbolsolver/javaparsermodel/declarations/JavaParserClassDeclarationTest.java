package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.google.common.collect.ImmutableSet;
import me.tomassetti.symbolsolver.AbstractTest;
import me.tomassetti.symbolsolver.model.declarations.AccessLevel;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.List;
import java.util.Set;
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

    ///
    /// Test fields
    ///

    @Test
    public void testGetFieldForExistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        FieldDeclaration fieldDeclaration = null;

        // declared field
        fieldDeclaration = constructorDeclaration.getField("modifiers");
        assertEquals("modifiers", fieldDeclaration.getName());
        assertEquals("java.util.EnumSet", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessLevel.PRIVATE, fieldDeclaration.accessLevel());
        assertEquals(false, fieldDeclaration.isStatic());

        // inherited field
        fieldDeclaration = constructorDeclaration.getField("annotations");
        assertEquals("annotations", fieldDeclaration.getName());
        assertEquals("java.util.List", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessLevel.PRIVATE, fieldDeclaration.accessLevel());
    }

    @Test(expected = UnsolvedSymbolException.class)
    public void testGetFieldForUnexistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        constructorDeclaration.getField("unexisting");
    }

    @Test
    public void testGetAllFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<FieldDeclaration> allFields = constructorDeclaration.getAllFields();
        assertEquals(16, allFields.size());

        FieldDeclaration fieldDeclaration = null;

        fieldDeclaration = allFields.get(0);
        assertEquals("modifiers", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("typeParameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("name", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(3);
        assertEquals("parameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(4);
        assertEquals("throws_", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(5);
        assertEquals("body", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(6);
        assertEquals("annotations", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(7);
        assertEquals("NODE_BY_BEGIN_POSITION", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(8);
        assertEquals("range", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(9);
        assertEquals("parentNode", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(10);
        assertEquals("childrenNodes", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(11);
        assertEquals("orphanComments", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(12);
        assertEquals("userData", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(13);
        assertEquals("comment", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(14);
        assertEquals("ABSOLUTE_BEGIN_LINE", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(15);
        assertEquals("ABSOLUTE_END_LINE", fieldDeclaration.getName());
    }

    @Test
    public void testGetAllStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<FieldDeclaration> allFields = constructorDeclaration.getAllStaticFields();
        assertEquals(3, allFields.size());

        FieldDeclaration fieldDeclaration = null;

        fieldDeclaration = allFields.get(0);
        assertEquals("NODE_BY_BEGIN_POSITION", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("ABSOLUTE_BEGIN_LINE", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("ABSOLUTE_END_LINE", fieldDeclaration.getName());
    }

    @Test
    public void testGetAllNonStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<FieldDeclaration> allFields = constructorDeclaration.getAllNonStaticFields();
        assertEquals(13, allFields.size());

        FieldDeclaration fieldDeclaration = null;

        fieldDeclaration = allFields.get(0);
        assertEquals("modifiers", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("typeParameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("name", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(3);
        assertEquals("parameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(4);
        assertEquals("throws_", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(5);
        assertEquals("body", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(6);
        assertEquals("annotations", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(7);
        assertEquals("range", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(8);
        assertEquals("parentNode", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(9);
        assertEquals("childrenNodes", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(10);
        assertEquals("orphanComments", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(11);
        assertEquals("userData", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(12);
        assertEquals("comment", fieldDeclaration.getName());
    }

    @Test
    public void testGetDeclaredFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<FieldDeclaration> allFields = constructorDeclaration.getDeclaredFields();
        assertEquals(6, allFields.size());

        FieldDeclaration fieldDeclaration = null;

        fieldDeclaration = allFields.get(0);
        assertEquals("modifiers", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("typeParameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("name", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(3);
        assertEquals("parameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(4);
        assertEquals("throws_", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(5);
        assertEquals("body", fieldDeclaration.getName());
    }

    ///
    /// Test methods
    ///

    @Test
    public void testGetDeclaredMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<MethodDeclaration> allMethods = constructorDeclaration.getDeclaredMethods();
        assertEquals(20, allMethods.size());

        List<MethodDeclaration> sortedMethods = allMethods.stream()
                .sorted((o1, o2) -> o1.getQualifiedSignature().compareTo(o2.getQualifiedSignature()))
                .collect(Collectors.toList());

        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.GenericVisitor<R, A>, A)", sortedMethods.get(0).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.VoidVisitor<A>, A)", sortedMethods.get(1).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getBody()", sortedMethods.get(2).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString()", sortedMethods.get(3).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean)", sortedMethods.get(4).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean, boolean)", sortedMethods.get(5).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getJavaDoc()", sortedMethods.get(6).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getModifiers()", sortedMethods.get(7).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getName()", sortedMethods.get(8).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getNameExpr()", sortedMethods.get(9).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getParameters()", sortedMethods.get(10).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getThrows()", sortedMethods.get(11).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getTypeParameters()", sortedMethods.get(12).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setBody(com.github.javaparser.ast.stmt.BlockStmt)", sortedMethods.get(13).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setModifiers(java.util.EnumSet<com.github.javaparser.ast.Modifier>)", sortedMethods.get(14).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setName(java.lang.String)", sortedMethods.get(15).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setNameExpr(com.github.javaparser.ast.expr.NameExpr)", sortedMethods.get(16).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setParameters(java.util.List<com.github.javaparser.ast.body.Parameter>)", sortedMethods.get(17).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setThrows(java.util.List<com.github.javaparser.ast.type.ReferenceType>)", sortedMethods.get(18).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setTypeParameters(java.util.List<com.github.javaparser.ast.type.TypeParameter>)", sortedMethods.get(19).getQualifiedSignature());
    }

    ///
    /// Test constructors
    ///
}
