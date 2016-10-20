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

package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.List;

import static me.tomassetti.symbolsolver.javaparser.Navigator.getParentNode;

public class ForStatementContext extends AbstractJavaParserContext<ForStmt> {

    public ForStatementContext(ForStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Expression expression : wrappedNode.getInit()) {
            if (expression instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expression;
                for (VariableDeclarator variableDeclarator : variableDeclarationExpr.getVariables()) {
                    if (variableDeclarator.getId().getName().equals(name)) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver));
                    }
                }
            } else {
                throw new UnsupportedOperationException(expression.getClass().getCanonicalName());
            }
        }

        if (getParentNode(wrappedNode) instanceof BlockStmt) {
            return StatementContext.solveInBlock(name, typeSolver, wrappedNode);
        } else {
            return getParent().solveSymbol(name, typeSolver);
        }

    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, argumentsTypes, typeSolver);
    }
}
