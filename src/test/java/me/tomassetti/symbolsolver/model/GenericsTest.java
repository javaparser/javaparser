package me.tomassetti.symbolsolver.model;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparser.Navigator;
import me.tomassetti.symbolsolver.model.javaparser.contexts.MethodCallExprContext;
import me.tomassetti.symbolsolver.model.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;
import org.junit.Test;

import java.io.InputStream;
import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class GenericsTest extends AbstractTest{

    @Test
    public void resolveFieldWithGenericTypeToString() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "s");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("s", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("s", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("java.lang.String", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveFieldWithGenericTypeToDeclaredClass() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "g");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("g", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("g", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("me.tomassetti.symbolsolver.javaparser.Generics", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveFieldWithGenericTypeToInteger() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "i");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("i", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("i", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(1, typeUsage.parameters().size());
        assertEquals("java.lang.Integer", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveFieldOfVariableType() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");
        VariableDeclarator field = Navigator.demandField(clazz, "a");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("a", field);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("a", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(true, typeUsage.isTypeVariable());
        assertEquals("A", typeUsage.getTypeName());
    }

    @Test
    public void resolveFieldOfGenericReferringToVariableType() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");
        VariableDeclarator field = Navigator.demandField(clazz, "as");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("as", field);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("as", symbolReference.get().getName());
        assertEquals(true, symbolReference.get().isField());

        TypeUsage typeUsage = symbolReference.get().getUsage();
        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.util.List", typeUsage.getTypeName());
        assertEquals(1, typeUsage.parameters().size());
        TypeUsage typeParam = typeUsage.parameters().get(0);
        assertEquals(true, typeParam.isTypeVariable());
        assertEquals("A", typeParam.getTypeName());
    }

    @Test
    public void resolveUsageOfGenericFieldSimpleCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");

        ExpressionStmt stmt = (ExpressionStmt)method.getBody().getStmts().get(0);
        Expression expression = stmt.getExpression();
        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.lang.String", typeUsage.getTypeName());
    }

    //PRIMA UN TEST CHE DICA CHE IL TIPO DEL CAMPO AS e' LIST<A> NON LIST<E>
    @Test
    public void resolveUsageOfGenericFieldIntermediateCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        VariableDeclarator field = Navigator.demandField(clazz, "as");

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(field);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.util.List", typeUsage.getTypeName());
        assertEquals(1, typeUsage.parameters().size());
        assertEquals(true, typeUsage.parameters().get(0).isTypeVariable());
        assertEquals("A", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveUsageOfGenericFieldAdvancedCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo2");

        ExpressionStmt stmt = (ExpressionStmt)method.getBody().getStmts().get(0);
        Expression expression = stmt.getExpression();
        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.util.List", typeUsage.getTypeName());
        assertEquals(1, typeUsage.parameters().size());
        assertEquals(false, typeUsage.parameters().get(0).isTypeVariable());
        assertEquals("java.lang.String", typeUsage.parameters().get(0).getTypeName());
    }

    @Test
    public void resolveElementOfList() throws ParseException {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a");
        Expression expression = variableDeclarator.getInit();

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("Comment", typeUsage.getTypeName());
    }

    @Test
    public void resolveElementOfListAdvancedExample() throws ParseException {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "annotations");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a");
        Expression expression = variableDeclarator.getInit();

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("AnnotationExpr", typeUsage.getTypeName());
    }

    @Test
    public void methodTypeParams() throws ParseException {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(call);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("void", typeUsage.getTypeName());
    }

    @Test
    public void classCastScope() throws ParseException {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        MethodCallExpr call = Navigator.findMethodCall(method, "cast");

        TypeSolver typeSolver = new JreTypeSolver();
        Expression scope = call.getScope();
        TypeUsage typeUsage = JavaParserFacade.get(typeSolver).getType(scope);

        System.out.println(typeUsage);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.lang.Class<N>", typeUsage.getTypeNameWithParams());
    }

    @Test
    public void classCast() throws ParseException {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(returnStmt.getExpr());

        assertEquals(true, typeUsage.isTypeVariable());
        assertEquals("N", typeUsage.getTypeNameWithParams());
    }

    @Test
    public void typeParamOnReturnTypeStep1() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ThisExpr thisExpr = Navigator.findNodeOfGivenClass(method, ThisExpr.class);

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(thisExpr);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("TypeParamOnReturnType", typeUsage.getTypeNameWithParams());
    }

    @Test
    public void typeParamOnReturnTypeStep2() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        NameExpr n1 = Navigator.findNameExpression(method, "n1");

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(n1);

        assertEquals(true, typeUsage.isTypeVariable());
        assertEquals("T", typeUsage.getTypeNameWithParams());
    }

    @Test
    public void typeParamOnReturnTypeStep3() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(call);

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("java.lang.Boolean", typeUsage.getTypeNameWithParams());
    }

    @Test
    public void typeParamOnReturnType() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeUsage typeUsage = JavaParserFacade.get(new JreTypeSolver()).getType(returnStmt.getExpr());

        assertEquals(false, typeUsage.isTypeVariable());
        assertEquals("boolean", typeUsage.getTypeNameWithParams());
    }
}
