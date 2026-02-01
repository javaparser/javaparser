package com.github.javaparser.key;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (23.06.23)
 */
public class LogicalTypes {
    @Test
    void resolveFree() {
        CompilationUnit cu = StaticJavaParser.parse("public class A { public ghost \\free test; " +
                "public \\map abc() { return test;} }");

        TypeSolver typeSolver = new TypeSolverBuilder()
                .withCurrentJRE()
                .with(new LogicalTypeSolver())
                .build();
        JavaSymbolSolver solver = new JavaSymbolSolver(typeSolver);
        solver.inject(cu);

        MethodDeclaration md = cu.getType(0).getMethodsByName("abc").get(0);
        Type retType = md.getType();
        System.out.println(retType);
        ResolvedType rt = retType.resolve();
        System.out.println(rt);

        ResolvedType testType = md.getBody().get().getStatement(0).asReturnStmt().getExpression().get().calculateResolvedType();
        System.out.println(testType);
    }

    private class LogicalTypeSolver implements TypeSolver {
        private TypeSolver parent;

        @Override
        public TypeSolver getParent() {
            return parent;
        }

        @Override
        public void setParent(TypeSolver parent) {
            this.parent = parent;
        }

        @Override
        public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
            return SymbolReference.solved(new ResolvedLogicTypeDeclaration(name));
        }

        @Override
        public SymbolReference<ResolvedReferenceTypeDeclaration>
        tryToSolveTypeInModule(String qualifiedModuleName, String simpleTypeName) {
            return tryToSolveType(simpleTypeName);
        }

        private static class ResolvedLogicTypeDeclaration implements ResolvedReferenceTypeDeclaration {
            private final String name;

            public ResolvedLogicTypeDeclaration(String name) {
                this.name = name;
            }

            @Override
            public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
                return Collections.emptyList();
            }

            @Override
            public List<ResolvedFieldDeclaration> getAllFields() {
                return Collections.emptyList();
            }

            @Override
            public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
                return Collections.emptySet();
            }

            @Override
            public Set<MethodUsage> getAllMethods() {
                return Collections.emptySet();
            }

            @Override
            public boolean isAssignableBy(ResolvedType type) {
                return false;
            }

            @Override
            public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
                return false;
            }

            @Override
            public boolean hasDirectlyAnnotation(String qualifiedName) {
                return false;
            }

            @Override
            public boolean isFunctionalInterface() {
                return false;
            }

            @Override
            public List<ResolvedConstructorDeclaration> getConstructors() {
                return Collections.emptyList();
            }

            @Override
            public Optional<ResolvedReferenceTypeDeclaration> containerType() {
                return Optional.empty();
            }

            @Override
            public String getPackageName() {
                return "";
            }

            @Override
            public String getClassName() {
                return name;
            }

            @Override
            public String getQualifiedName() {
                return name;
            }

            @Override
            public String getName() {
                return name;
            }

            @Override
            public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
                return Collections.emptyList();
            }
        }
    }
}
