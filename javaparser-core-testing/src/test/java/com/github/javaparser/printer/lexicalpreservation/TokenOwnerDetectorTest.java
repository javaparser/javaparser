package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import org.junit.jupiter.api.Test;

/**
 * Tests for TokenOwnerDetector and its strategies.
 */
class TokenOwnerDetectorTest {

    // Helper method to parse and find nodes
    private CompilationUnit parse(String code) {
        return StaticJavaParser.parse(code);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Variable Contexts
    // =========================================================================

    @Test
    void typeInLocalVariableDeclaration() {
        CompilationUnit cu = parse("class X { void m() { Set<String> x; } }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof VariableDeclarationExpr);
    }

    @Test
    void typeInFieldDeclaration() {
        CompilationUnit cu = parse("class X { Set<String> field; }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof FieldDeclaration);
    }

    @Test
    void typeInEnumConstant() {
        CompilationUnit cu = parse("enum X { A(new ArrayList<String>()); X(List<String> l) {} }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("ArrayList"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof EnumConstantDeclaration);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Parameter Contexts
    // =========================================================================

    @Test
    void typeInMethodParameter() {
        CompilationUnit cu = parse("class X { void m(Set<String> param) {} }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof Parameter);
    }

    @Test
    void typeInConstructorParameter() {
        CompilationUnit cu = parse("class X { X(Set<String> param) {} }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof Parameter);
    }

    @Test
    void typeInReceiverParameter() {
        CompilationUnit cu = parse("class X { void m(X X.this) {} }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("X"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof ReceiverParameter);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Method Contexts
    // =========================================================================

    @Test
    void typeInMethodReturnType() {
        CompilationUnit cu = parse("class X { Set<String> m() { return null; } }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof MethodDeclaration);
    }

    @Test
    void typeInAnnotationMemberDeclaration() {
        CompilationUnit cu = parse("@interface X { Set<String> value(); }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof AnnotationMemberDeclaration);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Class Contexts
    // =========================================================================

    @Test
    void typeInExtendsClause() {
        CompilationUnit cu = parse("class X extends ArrayList<String> {}");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("ArrayList"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    void typeInImplementsClause() {
        CompilationUnit cu = parse("class X implements List<String> {}");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof ClassOrInterfaceDeclaration);
    }

    @Test
    void typeInRecordImplementsClause() {
        StaticJavaParser.getConfiguration().setLanguageLevel(LanguageLevel.BLEEDING_EDGE);
        CompilationUnit cu = StaticJavaParser.parse("record X() implements List<String> {}");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof RecordDeclaration);
    }

    @Test
    void typeInEnumImplementsClause() {
        CompilationUnit cu = parse("enum X implements List<String> { A }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("List"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof EnumDeclaration);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Expression Contexts
    // =========================================================================

    @Test
    void typeInCastExpression() {
        CompilationUnit cu = parse("class X { void m() { Object o = (String) obj; } }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("String"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof CastExpr);
    }

    @Test
    void typeInInstanceOfExpression() {
        CompilationUnit cu = parse("class X { void m() { if (obj instanceof String) {} } }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("String"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof InstanceOfExpr);
    }

    @Test
    void typeInRecordPatternExpression() {
        StaticJavaParser.getConfiguration().setLanguageLevel(LanguageLevel.BLEEDING_EDGE);
        CompilationUnit cu = StaticJavaParser.parse("class X { void m() { switch (a) { case Box(String s) -> {} } } }");
        ClassOrInterfaceType type = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Box"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof RecordPatternExpr);
    }

    // =========================================================================
    // TypeOwnerStrategy Tests - Issue #3365 (nested generics)
    // =========================================================================

    @Test
    void nestedGenericsInVariableDeclaration() {
        CompilationUnit cu = parse("class X { void m() { Set<Pair<String, String>> x; } }");
        ClassOrInterfaceType pairType = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Pair"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(pairType);

        assertTrue(owner instanceof VariableDeclarationExpr, "Token owner should be VariableDeclarationExpr");
    }

    @Test
    void deeplyNestedGenerics() {
        CompilationUnit cu = parse("class X { Map<String, List<Set<Integer>>> map; }");
        ClassOrInterfaceType setType = cu.findFirst(
                        ClassOrInterfaceType.class, t -> t.getNameAsString().equals("Set"))
                .get();

        Node owner = TokenOwnerDetector.findTokenOwner(setType);

        assertTrue(owner instanceof FieldDeclaration);
    }

    // =========================================================================
    // needsRegeneration() Tests
    // =========================================================================

    @Test
    void needsRegenerationWhenTokenOwnerDiffersAndReplacedIsType() {
        CompilationUnit cu = parse("class X { Set<String> field; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();
        ClassOrInterfaceType type = cu.findFirst(ClassOrInterfaceType.class).get();

        Node tokenOwner = TokenOwnerDetector.findTokenOwner(type);
        Node parent = type.getParentNode().get(); // Should be Type node

        boolean needs = TokenOwnerDetector.needsRegeneration(parent, tokenOwner, type);

        assertTrue(needs, "Should need regeneration when token owner differs from parent and replaced is Type");
    }

    @Test
    void doesNotNeedRegenerationWhenTokenOwnerEqualsParent() {
        CompilationUnit cu = parse("class X { void m() { x = 5; } }");
        IntegerLiteralExpr literal = cu.findFirst(IntegerLiteralExpr.class).get();

        Node tokenOwner = TokenOwnerDetector.findTokenOwner(literal);
        Node parent = literal.getParentNode().get();

        boolean needs = TokenOwnerDetector.needsRegeneration(parent, tokenOwner, literal);

        assertFalse(needs, "Should not need regeneration when token owner equals parent");
    }

    @Test
    void doesNotNeedRegenerationForMultipleVariableDeclarations() {
        CompilationUnit cu = parse("class X { int a, b; }");
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();
        Type type = field.getVariable(0).getType();

        Node tokenOwner = TokenOwnerDetector.findTokenOwner(type);
        Node parent = type.getParentNode().get();

        boolean needs = TokenOwnerDetector.needsRegeneration(parent, tokenOwner, type);

        assertFalse(needs, "Should not need regeneration for multiple variable declarations (workaround)");
    }

    @Test
    void needsRegenerationWhenReplacedNodeIsWithinType() {
        CompilationUnit cu = parse("class X { Set<String> field; }");
        ClassOrInterfaceType stringType = cu.findAll(ClassOrInterfaceType.class).stream()
                .filter(t -> t.getNameAsString().equals("String"))
                .findFirst()
                .get();

        Node tokenOwner = TokenOwnerDetector.findTokenOwner(stringType);
        Node parent = stringType.getParentNode().get(); // TypeArguments

        boolean needs = TokenOwnerDetector.needsRegeneration(parent, tokenOwner, stringType);

        assertTrue(needs, "Should need regeneration when replaced node is within a Type");
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    @Test
    void typeOwnerForPrimitiveType() {
        CompilationUnit cu = parse("class X { int field; }");
        PrimitiveType type = cu.findFirst(PrimitiveType.class).get();

        Node owner = TokenOwnerDetector.findTokenOwner(type);

        assertTrue(owner instanceof FieldDeclaration);
    }

    @Test
    void typeOwnerForArrayType() {
        CompilationUnit cu = parse("class X { String[] field; }");
        ArrayType arrayType = cu.findFirst(ArrayType.class).get();

        Node owner = TokenOwnerDetector.findTokenOwner(arrayType);

        assertTrue(owner instanceof FieldDeclaration);
    }

    @Test
    void typeOwnerForVarType() {
        CompilationUnit cu = parse("class X { void m() { var x = \"hello\"; } }");
        VarType varType = cu.findFirst(VarType.class).get();

        Node owner = TokenOwnerDetector.findTokenOwner(varType);

        assertTrue(owner instanceof VariableDeclarationExpr);
    }

    @Test
    void typeOwnerForWildcardType() {
        CompilationUnit cu = parse("class X { List<?> field; }");
        WildcardType wildcardType = cu.findFirst(WildcardType.class).get();

        Node owner = TokenOwnerDetector.findTokenOwner(wildcardType);

        assertTrue(owner instanceof FieldDeclaration);
    }

    @Test
    void typeOwnerWhenNoOwnerFound() {
        // Create orphan type node (not in AST)
        ClassOrInterfaceType orphanType = new ClassOrInterfaceType(null, "Orphan");

        Node owner = TokenOwnerDetector.findTokenOwner(orphanType);

        assertEquals(orphanType, owner, "Should return the node itself when no owner found");
    }

    @Test
    void typeOwnerForNonTypeNode() {
        CompilationUnit cu = parse("class X { void m() { x = 5; } }");
        IntegerLiteralExpr literal = cu.findFirst(IntegerLiteralExpr.class).get();

        Node owner = TokenOwnerDetector.findTokenOwner(literal);

        assertEquals(literal, owner, "Should return the node itself for non-Type nodes");
    }
}
