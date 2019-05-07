package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter.NODE_TEXT_DATA;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

class LexicalPreservingPrinterTest extends AbstractLexicalPreservingTest {
    private NodeText getTextForNode(Node node) {
        return node.getData(NODE_TEXT_DATA);
    }


    //
    // Tests on TextNode definition
    //

    @Test
    void checkNodeTextCreatedForSimplestClass() {
        considerCode("class A {}");

        // CU
        assertEquals(1, getTextForNode(cu).numberOfElements());
        assertTrue(getTextForNode(cu).getTextElement(0) instanceof ChildTextElement);
        assertEquals(cu.getClassByName("A").get(), ((ChildTextElement) getTextForNode(cu).getTextElement(0)).getChild());

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
        assertTrue(getTextForNode(classA).getTextElement(6) instanceof TokenTextElement);
        assertEquals(GeneratedJavaParserConstants.EOF, ((TokenTextElement) getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(fd);
        assertEquals(Arrays.asList("int", " ", "i", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForVariableDeclarator() {
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
    void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethodParameter() {
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
    void checkNodeTextCreatedForPrimitiveType() {
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
    void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(imp);
        assertEquals(Arrays.asList("import", " ", "a.b.c.D", ";", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void addedImportShouldBePrependedWithEOL() {
        considerCode("import a;" + EOL + "class X{}");

        cu.addImport("b");

        assertEqualsNoEol("import a;\nimport b;\nclass X{}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void checkNodeTextCreatedGenericType() {
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
    void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(ad);
        assertEquals(Arrays.asList("public", " ", "@", "interface", " ", "ClassPreamble", " ", "{", " ", "String author();", " ", "}", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = ad.getMember(0).asAnnotationMemberDeclaration();
        Type type = md.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(type);
        assertEquals(Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5).asAnnotationMemberDeclaration();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWithoutExpression() {
        considerExpression("new int[]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty()).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWith() {
        considerExpression("new int[123]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "123", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty()).collect(Collectors.toList()));
    }

    //
    // Tests on findIndentation
    //

    @Test
    void findIndentationForAnnotationMemberDeclarationWithoutComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(4);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
    }

    //
    // Tests on printing
    //

    @Test
    void printASuperSimpleCUWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASuperSimpleClassWithAFieldAdded() {
        String code = "class A {}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        classA.addField("int", "myField");
        assertEquals("class A {" + EOL + "    int myField;" + EOL + "}", LexicalPreservingPrinter.print(classA));
    }

    @Test
    void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
    }

    @Test
    void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t" + EOL + " int f;" + EOL + EOL + EOL + "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
        assertEquals("void foo(int p  ) { return  'z'  \t; }", LexicalPreservingPrinter.print(cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t" + EOL +
                " int f;" + EOL + EOL + EOL +
                "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t" + EOL +
                EOL +
                "         void foo(int p  ) { return  'z'  \t; }}", LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleClassRemovingAMethod() {
        String code = "class /*a comment*/ A {\t\t" + EOL +
                " int f;" + EOL + EOL + EOL +
                "         void foo(int p  ) { return  'z'  \t; }" + EOL +
                " int g;}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(1);
        assertEquals("class /*a comment*/ A {\t\t" + EOL +
                " int f;" + EOL + EOL + EOL +
                " int g;}", LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAStatement() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS
        ));
        NodeList<Statement> stmts = cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get().getStatements();
        stmts.add(s);
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        assertEquals("void foo(char p1, int p2) {" + EOL +
                "    10 + 2;" + EOL +
                "}", LexicalPreservingPrinter.print(m));
    }
    
    @Test
    void printASimpleMethodRemovingAStatementCRLF() {
    	printASimpleMethodRemovingAStatement("\r\n");
    }
    
    @Test
    void printASimpleMethodRemovingAStatementLF() {
    	printASimpleMethodRemovingAStatement("\n");
    }
    
    @Test
    void printASimpleMethodRemovingAStatementCR() {
    	printASimpleMethodRemovingAStatement("\r");
    }
    
    private void printASimpleMethodRemovingAStatement(String eol) {
    	String code = "class A {" 						+ eol
    			+ "\t"		+  "foo(int a, int b) {"	+ eol
    			+ "\t\t" 	+ "int result = a * b;"		+ eol
    			+ "\t\t" 	+ "return a * b;"			+ eol
    			+ "\t"		+ "}"						+ eol
    			+ "}";
    			
    	
    	CompilationUnit cu = parse(code);
    	LexicalPreservingPrinter.setup(cu);
    	ExpressionStmt stmt = cu.findAll(ExpressionStmt.class).get(0);
    	stmt.remove();
    	
        assertEquals("class A {"						+ eol
    			+ "\t"		+  "foo(int a, int b) {"	+ eol
    			+ "\t\t" 	+ "return a * b;"			+ eol
    			+ "\t"		+ "}"						+ eol
    			+ "}", LexicalPreservingPrinter.print(cu)); 
    }
    
    @Test
    void printASimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import a.b.c.D;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void printAnotherImport() {
        String code = "import com.github.javaparser.ast.CompilationUnit;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import com.github.javaparser.ast.CompilationUnit;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void printAStaticImport() {
        String code = "import static com.github.javaparser.ParseStart.*;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import static com.github.javaparser.ParseStart.*;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void checkAnnidatedTypeParametersPrinting() {
        String code = "class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }";
        considerCode(code);
        assertEquals("class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASingleCatch() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception e) {}}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAMultiCatch() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception | AssertionError e) {}}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASingleCatchType() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Type catchType = catchClause.getParameter().getType();

        assertEquals("Exception", LexicalPreservingPrinter.print(catchType));
    }

    @Test
    void printUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        UnionType unionType = (UnionType) catchClause.getParameter().getType();

        assertEquals("Exception | AssertionError", LexicalPreservingPrinter.print(unionType));
    }

    @Test
    void printParameterHavingUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Parameter parameter = catchClause.getParameter();

        assertEquals("Exception | AssertionError e", LexicalPreservingPrinter.print(parameter));
    }

    @Test
    void printLambaWithUntypedParams() {
        String code = "class A {Function<String,String> f = a -> a;}";
        considerCode(code);

        assertEquals("class A {Function<String,String> f = a -> a;}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAModuleInfoSpecificKeywordUsedAsIdentifier1() {
        considerCode("class module { }");

        cu.getClassByName("module").get().setName("xyz");

        assertEquals("class xyz { }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAModuleInfoSpecificKeywordUsedAsIdentifier2() {
        considerCode("class xyz { }");

        cu.getClassByName("xyz").get().setName("module");

        assertEquals("class module { }", LexicalPreservingPrinter.print(cu));
    }

    // Issue 823: setPackageDeclaration on CU starting with a comment
    @Test
    void reactToSetPackageDeclarationOnCuStartingWithComment() {
        considerCode("// Hey, this is a comment\n" +
                "\n" +
                "\n" +
                "// Another one\n" +
                "\n" +
                "class A {}");
        cu.setPackageDeclaration("org.javaparser.lexicalpreservation.examples");
    }

    @Test
    void printLambdaIntersectionTypeAssignment() {
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
    void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    // See issue #855
    @Test
    void handleOverrideAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
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
    void preserveSpaceAsIsForASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");
        assertEquals(readExample("ASimpleClassWithMoreFormatting"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void renameASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step1"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void theLexicalPreservationStringForAnAddedMethodShouldBeIndented() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        assertEquals("public void setAField() {" + EOL +
                "    }", LexicalPreservingPrinter.print(setter));
    }

    @Test
    void addMethodToASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step2"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingParameterToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step3"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void findIndentationOfEmptyMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
    }

    @Test
    void findIndentationOfMethodWithStatements() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
        assertEquals(8, LexicalPreservingPrinter.findIndentation(setter.getBody().get().getStatement(0)).size());
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormattingFromStep3() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void nodeTextForMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Modifier.class));
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
    void nodeTextForModifiedMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN
                )));
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Modifier.class));
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
    void addASecondStatementToExistingMethod() throws IOException {
        considerExample("MethodWithOneStatement");

        MethodDeclaration methodDeclaration = cu.getType(0).getMethodsByName("someMethod").get(0);
        methodDeclaration.getBody().get().getStatements().add(new ExpressionStmt(
                new VariableDeclarationExpr(
                        new VariableDeclarator(
                                parseClassOrInterfaceType("String"),
                                "test2",
                                new StringLiteralExpr("")))
        ));
        assertEquals("public void someMethod() {" + EOL
                + "        String test = \"\";" + EOL
                + "        String test2 = \"\";" + EOL
        // HACK: The right closing brace should not have indentation because the original method did not introduce indentation, 
        //however due to necessity this test was left with indentation, in a later version it should be revised.
                + "    }", LexicalPreservingPrinter.print(methodDeclaration));
    }

    // See issue #866
    @Test
    void moveOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected @Override void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> member.ifMethodDeclaration(methodDeclaration -> {
                                if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                                    while (methodDeclaration.getAnnotations().isNonEmpty()) {
                                        AnnotationExpr annotationExpr = methodDeclaration.getAnnotations().get(0);
                                        annotationExpr.remove();
                                    }

                                    methodDeclaration.addMarkerAnnotation("Override");
                                }
                            })));
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
    void moveOrAddOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected @Override void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
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
                        }));
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
    void handleAddingMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   @Override" + EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> {
                            if (member instanceof MethodDeclaration) {
                                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                                    methodDeclaration.addMarkerAnnotation("Override");
                                }
                            }
                        }));
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
    void handleOverrideMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
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
    void handleOverrideAnnotationAlternative() {
        String code = "public class TestPage extends Page {" + EOL +
                EOL +
                "   protected void test() {}" + EOL +
                EOL +
                "   protected void initializePage() {}" + EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> member.ifMethodDeclaration(methodDeclaration -> methodDeclaration.addAnnotation("Override"))));
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
    void invokeModifierVisitor() {
        String code = "class A {" + EOL
                + "  Object f() {" + EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); " + EOL
                + "}}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new ModifierVisitor<>(), null);
    }

    @Test
    void handleDeprecatedAnnotationFinalClass() {
        String code = "public final class A {}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + EOL +
                "public final class A {}", LexicalPreservingPrinter.print(cu));

    }

    @Test
    void handleDeprecatedAnnotationAbstractClass() {
        String code = "public abstract class A {}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + EOL +
                "public abstract class A {}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void issue1244() {
        String code = "public class Foo {" + EOL + EOL
                + "// Some comment" + EOL + EOL // does work with only one \n
                + "public void writeExternal() {}" + EOL + "}";
        CompilationUnit originalCu = parse(code);
        CompilationUnit cu = LexicalPreservingPrinter.setup(originalCu);

        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(c -> {
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
    void testInvokeModifierVisitor() {
        String code = "class A {" + EOL +
                "  public String message = \"hello\";" + EOL +
                "   void bar() {" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "   }" + EOL +
                "}";

        CompilationUnit cu = parse(code);
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
    void invokeModifierVisitorIssue1297() {
        String code = "class A {" + EOL +
                "   public void bar() {" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "     System.out.println(\"hello\");" + EOL +
                "     // comment" + EOL +
                "   }" + EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new CallModifierVisitor(), null);
    }

    @Test
    void addedBlockCommentsPrinted() {
        String code = "public class Foo { }";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getClassByName("Foo").get()
                .addMethod("mymethod")
                .setBlockComment("block");
        assertEqualsNoEol("public class Foo {" + EOL +
                          "    /*block*/" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addedLineCommentsPrinted() {
        String code = "public class Foo { }";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getClassByName("Foo").get()
                .addMethod("mymethod")
                .setLineComment("line");
        assertEqualsNoEol("public class Foo {" + EOL +
                          "    //line" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}", LexicalPreservingPrinter.print(cu));
    }
    
    @Test
    void removedLineCommentsPrinted() {
        String code = "public class Foo {" + EOL +
                          "//line" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();

        assertEqualsNoEol("public class Foo {" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}", LexicalPreservingPrinter.print(cu));        
    }
    
    // Checks if comments get removed properly with Unix style line endings
    @Test
    void removedLineCommentsPrintedUnix() {
        String code = "public class Foo {" + "\n" +
                          "//line" + "\n" +
                          "void mymethod() {" + "\n" +
                          "}" + "\n" +
                          "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();
        
        assertEquals("public class Foo {" + "\n" +
                          "void mymethod() {" + "\n" +
                          "}" + "\n" +
                          "}", LexicalPreservingPrinter.print(cu));        
    }
    
    @Test
    void removedBlockCommentsPrinted() {
        String code = "public class Foo {" + EOL +
                          "/*" + EOL +
                          "Block comment coming through" + EOL +
                          "*/" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();

        assertEqualsNoEol("public class Foo {" + EOL +
                          "void mymethod() {" + EOL +
                          "}" + EOL +
                          "}", LexicalPreservingPrinter.print(cu));        
    }

    @Test
    void issue1321() {
        CompilationUnit compilationUnit = parse("class X { X() {} private void testme() {} }");
        LexicalPreservingPrinter.setup(compilationUnit);

        ClassOrInterfaceDeclaration type = compilationUnit.getClassByName("X").get();
        type.getConstructors().get(0).setBody(new BlockStmt().addStatement("testme();"));

        assertEqualsNoEol("class X { X() {\n    testme();\n} private void testme() {} }", LexicalPreservingPrinter.print(compilationUnit));
    }

    @Test
    void issue2001() {
        CompilationUnit compilationUnit = parse("class X {void blubb(){X.p(\"blaubb04\");}}");
        LexicalPreservingPrinter.setup(compilationUnit);

        compilationUnit
                .findAll(MethodCallExpr.class)
                .forEach(Node::removeForced);

        assertEqualsNoEol("class X {void blubb(){}}", LexicalPreservingPrinter.print(compilationUnit));
    }
}
