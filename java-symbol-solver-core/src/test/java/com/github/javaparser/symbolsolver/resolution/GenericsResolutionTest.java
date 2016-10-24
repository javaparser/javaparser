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
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ClassOrInterfaceDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ContextHelper;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class GenericsResolutionTest extends AbstractResolutionTest {

    @Test
    public void resolveFieldWithGenericTypeToString() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        VariableDeclarator fieldS = Navigator.demandField(clazz, "s");

        SymbolSolver symbolSolver = new SymbolSolver(new JreTypeSolver());
        Optional<Value> symbolReference = symbolSolver.solveSymbolAsValue("s", fieldS);

        assertEquals(true, symbolReference.isPresent());
        assertEquals("s", symbolReference.get().getName());

        Type type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.String", type.asReferenceType().typeParametersValues().get(0).describe());
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

        Type type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("me.tomassetti.symbolsolver.javaparser.Generics", type.asReferenceType().typeParametersValues().get(0).describe());
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

        Type type = symbolReference.get().getType();
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals("java.lang.Integer", type.asReferenceType().typeParametersValues().get(0).describe());
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

        Type type = symbolReference.get().getType();
        assertEquals(true, type.isTypeVariable());
        assertEquals("A", type.describe());
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

        Type type = symbolReference.get().getType();
        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<A>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        Type typeParam = type.asReferenceType().typeParametersValues().get(0);
        assertEquals(true, typeParam.isTypeVariable());
        assertEquals("A", typeParam.describe());
    }

    @Test
    public void resolveUsageOfGenericFieldSimpleCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");

        ExpressionStmt stmt = (ExpressionStmt) method.getBody().get().getStmts().get(0);
        Expression expression = stmt.getExpression();
        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.String", type.describe());
    }

    //PRIMA UN TEST CHE DICA CHE IL TIPO DEL CAMPO AS e' LIST<A> NON LIST<E>
    @Test
    public void resolveUsageOfGenericFieldIntermediateCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        VariableDeclarator field = Navigator.demandField(clazz, "as");

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(field);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<A>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals(true, type.asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("A", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveUsageOfGenericFieldAdvancedCase() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo2");

        ExpressionStmt stmt = (ExpressionStmt) method.getBody().get().getStmts().get(0);
        Expression expression = stmt.getExpression();
        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.util.List<java.lang.String>", type.describe());
        assertEquals(1, type.asReferenceType().typeParametersValues().size());
        assertEquals(false, type.asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("java.lang.String", type.asReferenceType().typeParametersValues().get(0).describe());
    }

    @Test
    public void resolveUsageOfMethodOfGenericClass() throws ParseException {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericMethodCalls.Derived");
        MethodDeclaration method = Navigator.demandMethod(clazz, "caller");
        MethodCallExpr expression = Navigator.findMethodCall(method, "callee");

        MethodUsage methodUsage = JavaParserFacade.get(new JreTypeSolver()).solveMethodAsUsage(expression);

        assertEquals("callee", methodUsage.getName());
    }

    @Test
    public void resolveElementOfList() throws ParseException {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a");
        Expression expression = variableDeclarator.getInit().get();

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("Comment", type.describe());
    }

    @Test
    public void resolveElementOfListAdvancedExample() throws ParseException {
        CompilationUnit cu = parseSample("ElementOfList");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ElementOfList");
        MethodDeclaration method = Navigator.demandMethod(clazz, "annotations");
        VariableDeclarator variableDeclarator = Navigator.demandVariableDeclaration(method, "a");
        Expression expression = variableDeclarator.getInit().get();

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(expression);

        assertEquals(false, type.isTypeVariable());
        assertEquals("AnnotationExpr", type.describe());
    }

    @Test
    public void genericsInheritance() throws ParseException {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");
        Expression thisRef = call.getArgs().get(0);

        TypeSolver typeSolver = new JreTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        Type voidVisitorAdapterOfA = javaParserFacade.getType(thisRef);
        List<ReferenceType> allAncestors = voidVisitorAdapterOfA.asReferenceType().getAllAncestors();
        assertEquals(2, allAncestors.size());
    }

    // Used to debug methodTypeParams
    @Test
    public void methodTypeParamsPrep() throws ParseException {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");
        Expression thisRef = call.getArgs().get(0);

        TypeSolver typeSolver = new JreTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        Type type = javaParserFacade.getType(thisRef);

        assertEquals(false, type.isTypeVariable());
        assertEquals("VoidVisitorAdapter<A>", type.describe());

        Expression arg = call.getArgs().get(1);

        type = javaParserFacade.getType(arg);

        assertEquals(true, type.isTypeVariable());
        assertEquals("A", type.describe());

        Expression javadoc = call.getScope().get();
        type = javaParserFacade.getType(javadoc);

        assertEquals(false, type.isTypeVariable());
        assertEquals("JavadocComment", type.describe());

        Context context = JavaParserFactory.getContext(call, typeSolver);
        List<Type> params = ImmutableList.of(javaParserFacade.getType(thisRef), javaParserFacade.getType(arg));

        ReferenceType javadocType = javaParserFacade.getType(javadoc).asReferenceType();

        TypeDeclaration typeDeclaration = javadocType.getTypeDeclaration();

        context = ContextHelper.getContext(typeDeclaration);
        List<com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration> methods = ((ClassOrInterfaceDeclarationContext) context).methodsByName("accept");
        com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration m;
        if (methods.get(0).getParam(0).getType().asReferenceType().getQualifiedName().equals("VoidVisitor")) {
            m = methods.get(0);
        } else {
            m = methods.get(1);
        }

        // FIXME fra gli antenati di VoidVisitorAdapter<A> non si trova VisitorAdapter<A>


        assertTrue(MethodResolutionLogic.isApplicable(m, "accept", params, typeSolver));


        // SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> res = MethodResolutionLogic.findMostApplicable(
        //methods, "accept", params, typeSolver);

        // SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> res = context.solveMethod("accept", params, typeSolver);

        // SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> res = typeDeclaration.solveMethod("accept", params, typeSolver);

        //SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> res = javadocType.solveMethod("accept", params, typeSolver);

        //SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> res = context.solveMethod(
        //        "accept", params, typeSolver);
        //assertTrue(res.isSolved());


        //assertTrue(JavaParserFacade.get(new JreTypeSolver()).solve(call).isSolved());
    }

    @Test
    public void methodTypeParams() throws ParseException {
        CompilationUnit cu = parseSample("MethodTypeParams");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "VoidVisitorAdapter");
        MethodDeclaration method = Navigator.demandMethod(clazz, "visit");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(call);

        assertEquals(false, type.isTypeVariable());
        assertEquals("void", type.describe());
    }

    @Test
    public void classCastScope() throws ParseException {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        MethodCallExpr call = Navigator.findMethodCall(method, "cast");

        TypeSolver typeSolver = new JreTypeSolver();
        Expression scope = call.getScope().get();
        Type type = JavaParserFacade.get(typeSolver).getType(scope);

        //System.out.println(typeUsage);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.Class<N>", type.describe());
    }

    @Test
    public void classCast() throws ParseException {
        CompilationUnit cu = parseSample("ClassCast");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassCast");
        MethodDeclaration method = Navigator.demandMethod(clazz, "getNodesByType");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(returnStmt.getExpr().get());

        assertEquals(true, type.isTypeVariable());
        assertEquals("N", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep1() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ThisExpr thisExpr = Navigator.findNodeOfGivenClass(method, ThisExpr.class);

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(thisExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("TypeParamOnReturnType", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep2() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        NameExpr n1 = Navigator.findNameExpression(method, "n1");

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(n1);

        assertEquals(true, type.isTypeVariable());
        assertEquals("T", type.describe());
    }

    @Test
    public void typeParamOnReturnTypeStep3() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        MethodCallExpr call = Navigator.findMethodCall(method, "accept");

        JavaParserFacade javaParserFacade = JavaParserFacade.get(new JreTypeSolver());
        Type type = javaParserFacade.getType(call);

        assertEquals(false, type.isTypeVariable());
        assertEquals("java.lang.Boolean", type.describe());
    }

    @Test
    public void typeParamOnReturnType() throws ParseException {
        CompilationUnit cu = parseSample("TypeParamOnReturnType");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "TypeParamOnReturnType");
        MethodDeclaration method = Navigator.demandMethod(clazz, "nodeEquals");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        Type type = JavaParserFacade.get(new JreTypeSolver()).getType(returnStmt.getExpr().get());

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }

    /*@Test
    public void genericCollectionWithWildcardsAndExtensionsPrep() throws ParseException {
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
    public void genericCollectionWithWildcardsAndExtensions() throws ParseException {
        CompilationUnit cu = parseSample("GenericCollectionWithExtension");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeSolver typeSolver = new JreTypeSolver();
        Expression returnStmtExpr = returnStmt.getExpr().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        Type type = javaParserFacade.getType(returnStmtExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }

    @Test
    public void methodWithGenericParameterTypes() throws ParseException {
        CompilationUnit cu = parseSample("GenericCollectionWithExtension");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        MethodCallExpr methodCall = Navigator.findMethodCall(method, "foo");

        TypeSolver typeSolver = new JreTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodUsage methodUsage = javaParserFacade.solveMethodAsUsage(methodCall);

        assertEquals("foo", methodUsage.getName());
    }

    @Test
    public void genericCollectionWithWildcards() throws ParseException {
        CompilationUnit cu = parseSample("GenericCollection");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Foo");
        MethodDeclaration method = Navigator.demandMethod(clazz, "bar");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);

        TypeSolver typeSolver = new JreTypeSolver();
        Expression returnStmtExpr = returnStmt.getExpr().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        Type type = javaParserFacade.getType(returnStmtExpr);

        assertEquals(false, type.isTypeVariable());
        assertEquals("boolean", type.describe());
    }
}
