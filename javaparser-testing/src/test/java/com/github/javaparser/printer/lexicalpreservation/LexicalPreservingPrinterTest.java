package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.*;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter.NODE_TEXT_DATA;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class LexicalPreservingPrinterTest extends AbstractLexicalPreservingTest {
    private NodeText getTextForNode(Node node) {
        return node.getData(NODE_TEXT_DATA);
    }


    //
    // Tests on TextNode definition
    //

    @Test
    public void checkNodeTextCreatedForSimplestClass() {
        considerCode("class A {}");

        // CU
        assertEquals(1, getTextForNode(cu).numberOfElements());
        assertEquals(true, getTextForNode(cu).getTextElement(0) instanceof ChildTextElement);
        assertEquals(cu.getClassByName("A").get(), ((ChildTextElement)getTextForNode(cu).getTextElement(0)).getChild());

        // Class
        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        assertEquals(7, getTextForNode(classA).numberOfElements());
        assertEquals("class", getTextForNode(classA).getTextElement(0).expand());
        assertEquals(" ", getTextForNode(classA).getTextElement(1).expand());
        assertEquals("A", getTextForNode(classA).getTextElement(2).expand());
        assertEquals(" ", getTextForNode(classA).getTextElement(3).expand());
        assertEquals("{", getTextForNode(classA).getTextElement(4).expand());
        assertEquals("}", getTextForNode(classA).getTextElement(5).expand());
        assertEquals("", getTextForNode(classA).getTextElement(6).expand());
        assertEquals(true, getTextForNode(classA).getTextElement(6) instanceof TokenTextElement);
        assertEquals(GeneratedJavaParserConstants.EOF, ((TokenTextElement)getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    public void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(fd);
        assertEquals(Arrays.asList("int", " ", "i", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForVariableDeclarator() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        VariableDeclarator vd = fd.getVariables().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(vd);
        assertEquals(Arrays.asList("i"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethodParameter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(p1);
        assertEquals(Arrays.asList("int", " ", "p1"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForPrimitiveType() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        Type t = p1.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(t);
        assertEquals(Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(imp);
        assertEquals(Arrays.asList("import", " ", "a.b.c.D", ";", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedGenericType() {
        String code = "class A {ParseResult<T> result;}";
        considerCode(code);

        FieldDeclaration field = cu.getClassByName("A").get().getFieldByName("result").get();
        Node t = field.getCommonType();
        Node t2 = field.getVariable(0).getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(field);
        assertEquals(Arrays.asList("ParseResult", "<", "T", ">", " ", "result", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(ad);
        assertEquals(Arrays.asList("public", " ", "@", "interface", " ", "ClassPreamble", " ", "{", " ", "String author();", " ", "}", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0).asAnnotationMemberDeclaration();
        Type type = md.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(type);
        assertEquals(Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5).asAnnotationMemberDeclaration();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedArrayCreationLevelWithoutExpression() throws IOException {
        considerExpression("new int[]");

        ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr)expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty()).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedArrayCreationLevelWith() throws IOException {
        considerExpression("new int[123]");

        ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr)expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "123", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty()).collect(Collectors.toList()));
    }

    //
    // Tests on findIndentation
    //

    @Test
    public void findIndentationForAnnotationMemberDeclarationWithoutComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(4);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
    }

    //
    // Tests on printing
    //

    @Test
    public void printASuperSimpleCUWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printASuperSimpleClassWithAFieldAdded() {
        String code = "class A {}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        classA.addField("int", "myField");
        assertEquals("class A {" + EOL + "    int myField;"+EOL+"}", LexicalPreservingPrinter.print(classA));
    }

    @Test
    public void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
    }

    @Test
    public void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t"+EOL+" int f;"+EOL+EOL+EOL+"         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
        assertEquals("void foo(int p  ) { return  'z'  \t; }", LexicalPreservingPrinter.print(cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    public void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t"+EOL+" int f;"+EOL+EOL+EOL+"         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t"+ EOL +
                EOL +
                "         void foo(int p  ) { return  'z'  \t; }}", LexicalPreservingPrinter.print(c));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleMethodAddingAStatement() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS
        ));
        NodeList<Statement> stmts = cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get().getStatements();
        stmts.add(s);
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        assertEquals("void foo(char p1, int p2) {"+EOL +
                "    10 + 2;"+ EOL +
                "}", LexicalPreservingPrinter.print(m));
    }

    @Test
    public void printASimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import a.b.c.D;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    public void printAnotherImport() {
        String code = "import com.github.javaparser.ast.CompilationUnit;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import com.github.javaparser.ast.CompilationUnit;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    public void printAStaticImport() {
        String code = "import static com.github.javaparser.ParseStart.*;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import static com.github.javaparser.ParseStart.*;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    public void checkAnnidatedTypeParametersPrinting() {
        String code = "class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }";
        considerCode(code);
        assertEquals("class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printASingleCatch() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception e) {}}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printAMultiCatch() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception | AssertionError e) {}}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printASingleCatchType() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Type catchType = catchClause.getParameter().getType();

        assertEquals("Exception", LexicalPreservingPrinter.print(catchType));
    }

    @Test
    public void printUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        UnionType unionType = (UnionType)catchClause.getParameter().getType();

        assertEquals("Exception | AssertionError", LexicalPreservingPrinter.print(unionType));
    }

    @Test
    public void printParameterHavingUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Parameter parameter = catchClause.getParameter();

        assertEquals("Exception | AssertionError e", LexicalPreservingPrinter.print(parameter));
    }

    @Test
    public void printLambaWithUntypedParams() {
        String code = "class A {Function<String,String> f = a -> a;}";
        considerCode(code);

        assertEquals("class A {Function<String,String> f = a -> a;}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printAModuleInfoSpecificKeywordUsedAsIdentifier1() {
        considerCode("class module { }");

        cu.getClassByName("module").get().setName("xyz");

        assertEquals("class xyz { }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printAModuleInfoSpecificKeywordUsedAsIdentifier2() {
        considerCode("class xyz { }");

        cu.getClassByName("xyz").get().setName("module");

        assertEquals("class module { }", LexicalPreservingPrinter.print(cu));
    }

    // Issue 823: setPackageDeclaration on CU starting with a comment
    @Test
    public void reactToSetPackageDeclarationOnCuStartingWithComment() {
        considerCode("// Hey, this is a comment\n" +
                "\n" +
                "\n" +
                "// Another one\n" +
                "\n" +
                "class A {}");
        cu.setPackageDeclaration("org.javaparser.lexicalpreservation.examples");
    }

    @Test
    public void printLambdaIntersectionTypeAssignment() {
        String code = "class A {" + EOL +
                "  void f() {" + EOL +
                "    Runnable r = (Runnable & Serializable) (() -> {});" + EOL +
                "    r = (Runnable & Serializable)() -> {};" + EOL +
                "    r = (Runnable & I)() -> {};" + EOL +
                "  }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    // See issue #855
    @Test
    public void handleOverrideAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> {
                            if (member instanceof MethodDeclaration) {
                                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                                    methodDeclaration.addAnnotation("Override");
                                }
                            }
                        }));
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   @Override()" + EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void preserveSpaceAsIsForASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");
        assertEquals(readExample("ASimpleClassWithMoreFormatting"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void renameASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step1"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void theLexicalPreservationStringForAnAddedMethodShouldBeIndented() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", Modifier.PUBLIC);
        assertEquals("public void setAField() {" + EOL +
                "    }", LexicalPreservingPrinter.print(setter));
    }

    @Test
    public void addMethodToASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", Modifier.PUBLIC);
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step2"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void addingParameterToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", Modifier.PUBLIC);
        setter.addParameter("boolean", "aField");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step3"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void findIndentationOfEmptyMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
    }

    @Test
    public void findIndentationOfMethodWithStatements() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
        assertEquals(8, LexicalPreservingPrinter.findIndentation(setter.getBody().get().getStatement(0)).size());
    }

    @Test
    public void addingStatementToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", Modifier.PUBLIC);
        setter.addParameter("boolean", "aField");
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),"aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void addingStatementToAnAddedMethodInASimpleClassWithMoreFormattingFromStep3() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),"aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void nodeTextForMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.PUBLIC));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(VoidType.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(SimpleName.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LPAREN));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Parameter.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RPAREN));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(BlockStmt.class));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get());
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LBRACE));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(ExpressionStmt.class));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RBRACE));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get().getStatement(0));
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(AssignExpr.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SEMICOLON));
        assertEquals(index, nodeText.getElements().size());
    }

    @Test
    public void nodeTextForModifiedMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),"aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.PUBLIC));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(VoidType.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(SimpleName.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LPAREN));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Parameter.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RPAREN));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(BlockStmt.class));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get());
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LBRACE));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(ExpressionStmt.class));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RBRACE));
        assertEquals(index, nodeText.getElements().size());

        nodeText = LexicalPreservingPrinter.getOrCreateNodeText(setter.getBody().get().getStatement(0));
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(AssignExpr.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SEMICOLON));
        assertEquals(index, nodeText.getElements().size());
    }

    // See issue #926
    @Test
    public void addASecondStatementToExistingMethod() throws IOException {
        considerExample("MethodWithOneStatement");

        MethodDeclaration methodDeclaration = cu.getType(0).getMethodsByName("someMethod").get(0);
        methodDeclaration.getBody().get().getStatements().add(new ExpressionStmt(
                new VariableDeclarationExpr(
                        new VariableDeclarator(
                                JavaParser.parseClassOrInterfaceType("String"),
                                "test2",
                                new StringLiteralExpr("")))
        ));
        assertEquals("public void someMethod() {" + EOL
                + "        String test = \"\";" + EOL
                + "        String test2 = \"\";" + EOL
                + "    }", LexicalPreservingPrinter.print(methodDeclaration));
    }

    // See issue #866
    @Test
    public void moveOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected @Override void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> {
                    type.getMembers()
                            .forEach(member -> {
                                member.ifMethodDeclaration(methodDeclaration -> {
                                    if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                                        while (methodDeclaration.getAnnotations().isNonEmpty()) {
                                            AnnotationExpr annotationExpr = methodDeclaration.getAnnotations().get(0);
                                            annotationExpr.remove();
                                        }

                                        methodDeclaration.addMarkerAnnotation("Override");
                                    }
                                });
                            });
                });
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #866
    @Test
    public void moveOrAddOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected @Override void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> {
                    type.getMembers()
                            .forEach(member -> {
                                if (member instanceof MethodDeclaration) {
                                    MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                    if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                                        while (methodDeclaration.getAnnotations().isNonEmpty()) {
                                            AnnotationExpr annotationExpr = methodDeclaration.getAnnotations().get(0);
                                            annotationExpr.remove();
                                        }
                                    }
                                    methodDeclaration.addMarkerAnnotation("Override");
                                }
                            });
                });
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    public void handleAddingMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> {
                    type.getMembers()
                            .forEach(member -> {
                                if (member instanceof MethodDeclaration) {
                                    MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                    if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                                        methodDeclaration.addMarkerAnnotation("Override");
                                    }
                                }
                            });
                });
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    public void handleOverrideMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member ->
                            member.ifMethodDeclaration(methodDeclaration -> methodDeclaration.addMarkerAnnotation("Override")
                        )));
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    public void handleOverrideAnnotationAlternative() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member ->  member.ifMethodDeclaration(methodDeclaration -> methodDeclaration.addAnnotation("Override"))));
        assertEquals("public class TestPage extends Page {" + EOL +
                EOL +
                "   @Override()" + EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override()" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void invokeModifierVisitor() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new ModifierVisitor<>(), null);
    }

    @Test
    public void handleDeprecatedAnnotationFinalClass() {
        String code = "public final class A {}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + EOL +
                "public final class A {}" , LexicalPreservingPrinter.print(cu));

    }

    @Test
    public void handleDeprecatedAnnotationAbstractClass() {
        String code = "public abstract class A {}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + EOL +
                "public abstract class A {}" , LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void issue1244() {
        String code = "public class Foo {" + EOL + EOL
                + "// Some comment" + EOL + EOL // does work with only one \n
                + "public void writeExternal() {}" + EOL + "}";
        CompilationUnit originalCu = JavaParser.parse(code);
        CompilationUnit cu = LexicalPreservingPrinter.setup(originalCu);

        cu.findAll(ClassOrInterfaceDeclaration.class).stream().forEach(c -> {
            List<MethodDeclaration> methods = c.getMethodsByName("writeExternal");
            for (MethodDeclaration method : methods) {
                c.remove(method);
            }
        });
        assertEqualsNoEol("public class Foo {\n" +
                "// Some comment\n\n" +
                "}", LexicalPreservingPrinter.print(cu));
    }

    static class AddFooCallModifierVisitor extends ModifierVisitor<Void> {
        @Override
        public Visitable visit(MethodCallExpr n, Void arg) {
            // Add a call to foo() on every found method call
            return new MethodCallExpr(n, "foo");
        }
    }

    // See issue 1277
    @Test
    public void testInvokeModifierVisitor() throws IOException {
        String code = "class A {" + EOL +
                "  public String message = \"hello\";" + EOL +
                "   void bar() {" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "   }" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new AddFooCallModifierVisitor(), null);
    }

    static class CallModifierVisitor extends ModifierVisitor<Void> {
        @Override
        public Visitable visit(MethodCallExpr n, Void arg) {
            // Add a call to foo() on every found method call
            return new MethodCallExpr(n.clone(), "foo");
        }
    }

    @Test
    public void invokeModifierVisitorIssue1297() {
        String code = "class A {" + EOL +
                "   public void bar() {" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "     // comment" + EOL +
                "   }" + EOL +
                "}";

        CompilationUnit cu = JavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new CallModifierVisitor(), null);
    }
}
