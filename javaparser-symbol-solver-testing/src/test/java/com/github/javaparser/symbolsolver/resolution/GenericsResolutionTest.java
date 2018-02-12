/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution;

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
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class GenericsResolutionTest extends AbstractResolutionTest {

    @Test
    public void resolveFieldWithGenericTypeToString() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "s");

        SymbolSolver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("s", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("s", symbolReference.get().getName());

        ResolvedType type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.String", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveFieldWithGenericTypeToDeclaredClass() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "g");

        SymbolSolver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("g", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("g", symbolReference.get().getName());

        ResolvedType type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("me.tomassetti.symbolsolver.javaparser.Generics", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveFieldWithGenericTypeToInteger() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "i");

        SymbolSolver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("i", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("i", symbolReference.get().getName());

        ResolvedType type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.Integer", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveFieldOfVariableType() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");
        VariableDeclarator field = Navigator.demandField(clazz, "a");

        SymbolSolver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("a", field);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("a", symbolReference.get().getName());

        ResolvedType type = symbolReference.get().getType();
        assertEquals(true, type.isTypeVariable());
        assertEquals("A", type.describe());
    }

    @Test
    public void resolveFieldOfGenericReferringToVariableType() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");
        VariableDeclarator field = Navigator.demandField(clazz, "as");

        SymbolSolver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("as", field);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("as", symbolReference.get().getName());

        ResolvedType type = symbolReference.get().getType();
        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<A>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        ResolvedType typeParam = type.asReferenceType().typeParametersValues().get(0);
        assertEquals(true, typeParam.isTypeVariable());
        assertEquals("A", typeParam.describe());
    }

    @Test
    public void resolveUsageOfGenericFieldSimpleCase() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");

        ExpressionStmt stmt = (ExpressionStmt) method.getBody().get().getStatements().get(0);
        Expression expression = stmt.getExpression();
        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.String", type.describe());
    }

    //PRIMA UN TEST CHE DICA CHE IL TIPO DEL CAMPO AS e' LIST<A> NON LIST<E>
    @Test
    public void resolveUsageOfGenericFieldIntermediateCase() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        VariableDeclarator field = Navigator.demandField(clazz, "as");

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(field);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<A>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals(true, type.asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("A", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveUsageOfGenericFieldAdvancedCase() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo2");

        ExpressionStmt stmt = (ExpressionStmt) method.getBody().get().getStatements().get(0);
        Expression expression = stmt.getExpression();
        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<java.lang.String>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals(false, type.asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("java.lang.String", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveUsageOfMethodOfGenericClass() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericMethodCalls.Derived");
        MethodDeclaration method = Navigator.demandMethod(clazz, "caller");
        MethodCallExpr expression = Navigator.findMethodCall(method, "callee").get();

        MethodUsage methodUsage = JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(expression);

        assertEquals("callee", methodUsage.getName());
    }

    @Test
    public void resolveElementOfList() {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a").get();
        Expression expression = variableDeclarator.getInitializer().get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("Comment", type.describe());
    }

    @Test
    public void resolveElementOfListAdvancedExample() {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "annotations");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a").get();
        Expression expression = variableDeclarator.getInitializer().get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("AnnotationExpr", type.describe());
    }

    @Test
    public void genericsInheritance() {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept").get();
        Expression thisRef = call.getArguments().get(0);

        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        ResolvedType voidVisitorAdapterOfA = javaParserFacade.getType(thisRef);
        List<ResolvedReferenceType> allAncestors = voidVisitorAdapterOfA.asReferenceType().getAllAncestors();
        assertEquals(2, allAncestors.size());
    }

    @Test
    public void methodTypeParams() {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept").get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(call);

        assertEquals(false, type.isTypeVariable());
        assertEquals("void", type.describe());
    }

    @Test
    public void classCastScope() {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        MethodCallExpr call = Navigator.findMethodCall(method, "cast").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        Expression scope = call.getScope().get();
        ResolvedType type = JavaParserFacade.get(typeSolver).getType(scope);

        //System.out.println(typeUsage);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.Class<N>", type.describe());
    }

    @Test
    public void classCast() {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(returnStmt.getExpression().get());

        assertEquals(true, type.isTypeVariable());
        assertEquals("N", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep1() {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ThisExpr thisExpr = Navigator.findNodeOfGivenClass(method, ThisExpr.class);

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(thisExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("TypeParamOnReturnType", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep2() {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        NameExpr n1 = Navigator.findNameExpression(method, "n1").get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(n1);

        assertEquals(true, type.isTypeVariable());
        assertEquals("T", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep3() {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept").get();

        JavaParserFacade javaParserFacade = JavaParserFacade.get(new ReflectionTypeSolver());
        ResolvedType type = javaParserFacade.getType(call);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.Boolean", type.describe());
    }

    @Test
    public void typeParamOnReturnType() {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(returnStmt.getExpression().get());

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }

    /*@Test
    public void genericCollectionWithWildcardsAndExtensionsPrep() {
        CompilationUnit cu = parseSample("GenericCollectionWithExtension");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeSolver typeSolver = new JreTypeSolver();
        MethodCallExpr call = (MethodCallExpr) returnStmt.getExpr();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        List<TypeUsage> params = new ArrayList<>();
        if (call.getArgs() != null) {
            for (Expression param : call.getArgs()) {
                params.add(javaParserFacade.getType(param, false));
            }
        }
        Context context = JavaParserFactory.getContext(call, typeSolver);

        ReferenceTypeUsage typeOfScope = javaParserFacade.getType(call.getScope()).asReferenceType();
        me.tomassetti.symbolsolver.model.declarations.TypeDeclaration typeDeclaration = typeOfScope.getTypeDeclaration();
        List<TypeUsage> typeParametersValues = typeOfScope.typeParametersValues();

        List<MethodUsage> methods = new ArrayList<>();
        for (Method m : List.class.getMethods()) {
            if (m.getName().equals("addAll") && !m.isBridge() && !m.isSynthetic()) {
                me.tomassetti.symbolsolver.model.declarations.MethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(m, typeSolver);
                if (methods.size() == 0) {
                    // ok, e' il primo
                    ReferenceTypeUsage paramType = methodDeclaration.getParam(0).getType(typeSolver).asReferenceType();
                    assertTrue(paramType.asReferenceType().typeParametersValues().get(0).isWildcard());
                }
                MethodUsage mu = new MethodUsage(methodDeclaration, typeSolver);
                int i = 0;
                for (TypeParameter tp : typeDeclaration.getTypeParameters()) {
                    mu = mu.replaceTypeParameter(tp.getName(), typeParametersValues.get(i));
                    i++;
                }
                methods.add(mu);
            }

        }

        assertTrue(MethodResolutionLogic.isApplicable(methods.get(0), "addAll", params, typeSolver));
        //Optional<MethodUsage> methodUsage = MethodResolutionLogic.findMostApplicableUsage(methods, "addAll", params, typeSolver);

        //Optional<MethodUsage> methodUsage = typeDeclaration.solveMethodAsUsage("addAll", params, typeSolver, context, typeParametersValues);

        //Optional<MethodUsage> methodUsage = context.solveMethodAsUsage("addAll", params, typeSolver);

        //assertTrue(methodUsage.isPresent());

    }*/

    @Test
    public void genericCollectionWithWildcardsAndExtensions() {
        CompilationUnit cu = parseSample("GenericCollectionWithExtension");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeSolver typeSolver = new ReflectionTypeSolver();
        Expression returnStmtExpr = returnStmt.getExpression().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        ResolvedType type = javaParserFacade.getType(returnStmtExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }

    @Test
    public void methodWithGenericParameterTypes() {
        CompilationUnit cu = parseSample("GenericCollectionWithExtension");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        MethodCallExpr methodCall = Navigator.findMethodCall(method, "foo").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodUsage methodUsage = javaParserFacade.solveMethodAsUsage(methodCall);

        assertEquals("foo", methodUsage.getName());
    }

    @Test
    public void genericCollectionWithWildcards() {
        CompilationUnit cu = parseSample("GenericCollection");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeSolver typeSolver = new ReflectionTypeSolver();
        Expression returnStmtExpr = returnStmt.getExpression().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        ResolvedType type = javaParserFacade.getType(returnStmtExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }
}
