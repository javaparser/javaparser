package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.Providers;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.utils.Pair;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class LexicalPreservingPrinterTest extends AbstractLexicalPreservingTest {

    //
    // Tests on TextNode definition
    //

    @Test
    public void checkNodeTextCreatedForSimplestClass() {
        considerCode("class A {}");

        // CU
        assertEquals(1, lpp.getTextForNode(cu).numberOfElements());
        assertEquals(true, lpp.getTextForNode(cu).getTextElement(0) instanceof ChildTextElement);
        assertEquals(cu.getClassByName("A").get(), ((ChildTextElement)lpp.getTextForNode(cu).getTextElement(0)).getChild());

        // Class
        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        assertEquals(7, lpp.getTextForNode(classA).numberOfElements());
        assertEquals("class", lpp.getTextForNode(classA).getTextElement(0).expand());
        assertEquals(" ", lpp.getTextForNode(classA).getTextElement(1).expand());
        assertEquals("A", lpp.getTextForNode(classA).getTextElement(2).expand());
        assertEquals(" ", lpp.getTextForNode(classA).getTextElement(3).expand());
        assertEquals("{", lpp.getTextForNode(classA).getTextElement(4).expand());
        assertEquals("}", lpp.getTextForNode(classA).getTextElement(5).expand());
        assertEquals("", lpp.getTextForNode(classA).getTextElement(6).expand());
        assertEquals(true, lpp.getTextForNode(classA).getTextElement(6) instanceof TokenTextElement);
        assertEquals(GeneratedJavaParserConstants.EOF, ((TokenTextElement)lpp.getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    public void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = lpp.getOrCreateNodeText(fd);
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
        NodeText nodeText = lpp.getOrCreateNodeText(vd);
        assertEquals(Arrays.asList("i"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
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
        NodeText nodeText = lpp.getOrCreateNodeText(p1);
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
        NodeText nodeText = lpp.getOrCreateNodeText(t);
        assertEquals(Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(imp);
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
        NodeText nodeText = lpp.getOrCreateNodeText(field);
        assertEquals(Arrays.asList("ParseResult", "<", "T", ">", " ", "result", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = lpp.getOrCreateNodeText(ad);
        assertEquals(Arrays.asList("public", " ", "@", "interface", " ", "ClassPreamble", " ", "{", " ", "String author();", " ", "}", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        Type type = md.getType();
        NodeText nodeText = lpp.getOrCreateNodeText(type);
        assertEquals(Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedArrayCreationLevelWithoutExpression() throws IOException {
        considerExpression("new int[]");

        ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr)expression;
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty()).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedArrayCreationLevelWith() throws IOException {
        considerExpression("new int[123]");

        ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr)expression;
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(arrayCreationLevel);
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
        List<TokenTextElement> indentation = lpp.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(e -> e.expand()).collect(Collectors.toList()));
    }

    @Test
    public void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TokenTextElement> indentation = lpp.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(e -> e.expand()).collect(Collectors.toList()));
    }

    //
    // Tests on printing
    //

    @Test
    public void printASuperSimpleCUWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
    }

    @Test
    public void printASuperSimpleClassWithAFieldAdded() {
        String code = "class A {}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        classA.addField("int", "myField");
        assertEquals("class A {" + EOL + "    int myField;"+EOL+"}", lpp.print(classA));
    }

    @Test
    public void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, lpp.print(cu.getClassByName("A").get()));
    }

    @Test
    public void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t"+EOL+" int f;"+EOL+EOL+EOL+"         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
        assertEquals(code, lpp.print(cu.getClassByName("A").get()));
        assertEquals("void foo(int p  ) { return  'z'  \t; }", lpp.print(cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    public void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t"+EOL+" int f;"+EOL+EOL+EOL+"         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t"+ EOL +
                EOL +
                "         void foo(int p  ) { return  'z'  \t; }}", lpp.print(c));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", lpp.print(m));
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
                "}", lpp.print(m));
    }

    @Test
    public void printASimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import a.b.c.D;", lpp.print(imp));
    }

    @Test
    public void printAnotherImport() {
        String code = "import com.github.javaparser.ast.CompilationUnit;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import com.github.javaparser.ast.CompilationUnit;", lpp.print(imp));
    }

    @Test
    public void printAStaticImport() {
        String code = "import static com.github.javaparser.ParseStart.*;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import static com.github.javaparser.ParseStart.*;", lpp.print(imp));
    }

    @Test
    public void checkAnnidatedTypeParametersPrinting() {
        String code = "class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }";
        considerCode(code);
        assertEquals("class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }", lpp.print(cu));
    }

    @Test
    public void printASingleCatch() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception e) {}}}", lpp.print(cu));
    }

    @Test
    public void printAMultiCatch() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception | AssertionError e) {}}}", lpp.print(cu));
    }

    @Test
    public void printASingleCatchType() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Type catchType = catchClause.getParameter().getType();

        assertEquals("Exception", lpp.print(catchType));
    }

    @Test
    public void printUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        UnionType unionType = (UnionType)catchClause.getParameter().getType();

        assertEquals("Exception | AssertionError", lpp.print(unionType));
    }

    @Test
    public void printParameterHavingUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration)cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt)initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Parameter parameter = catchClause.getParameter();

        assertEquals("Exception | AssertionError e", lpp.print(parameter));
    }

    @Test
    public void printLambaWithUntypedParams() {
        String code = "class A {Function<String,String> f = a -> a;}";
        considerCode(code);

        assertEquals("class A {Function<String,String> f = a -> a;}", lpp.print(cu));
    }

    @Test
    public void printAModuleInfoSpecificKeywordUsedAsIdentifier1() {
        considerCode("class module { }");

        cu.getClassByName("module").get().setName("xyz");

        assertEquals("class xyz { }", lpp.print(cu));
    }

    @Test
    public void printAModuleInfoSpecificKeywordUsedAsIdentifier2() {
        considerCode("class xyz { }");

        cu.getClassByName("xyz").get().setName("module");

        assertEquals("class module { }", lpp.print(cu));
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

        assertEquals(code, lpp.print(cu));
    }

    @Test
    public void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
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

        Pair<ParseResult<CompilationUnit>, LexicalPreservingPrinter> result = LexicalPreservingPrinter
                .setup(ParseStart.COMPILATION_UNIT, Providers.provider(code));

        CompilationUnit cu = result.a.getResult().get();

        cu.getTypes().stream()
                .forEach(type -> type.getMembers().stream()
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
                "}", result.b.print(cu));
    }

    @Test
    public void preserveSpaceAsIsForASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");
        assertEquals(readExample("ASimpleClassWithMoreFormatting"), lpp.print(cu));
    }

    @Test
    public void renameASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step1"), lpp.print(cu));
    }

    @Test
    public void addMethodToASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", Modifier.PUBLIC);
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step2"), lpp.print(cu));
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
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step3"), lpp.print(cu));
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
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), lpp.print(cu));
    }

}
