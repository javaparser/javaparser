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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.List;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class SwitchEntryContext extends AbstractJavaParserContext<SwitchEntry> {

    public SwitchEntryContext(SwitchEntry wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        SwitchStmt switchStmt = (SwitchStmt) requireParentNode(wrappedNode);
        ResolvedType type = JavaParserFacade.get(typeSolver).getType(switchStmt.getSelector());
        if (type.isReferenceType() && type.asReferenceType().getTypeDeclaration().isEnum()) {
            if (type instanceof ReferenceTypeImpl) {
                ReferenceTypeImpl typeUsageOfTypeDeclaration = (ReferenceTypeImpl) type;
                if (typeUsageOfTypeDeclaration.getTypeDeclaration().asEnum().hasEnumConstant(name)) {
                    return SymbolReference.solved(typeUsageOfTypeDeclaration.getTypeDeclaration().asEnum().getEnumConstant(name));
                }
                if (typeUsageOfTypeDeclaration.getTypeDeclaration().hasField(name)) {
                    return SymbolReference.solved(typeUsageOfTypeDeclaration.getTypeDeclaration().getField(name));
                }
            } else {
                throw new UnsupportedOperationException();
            }
        }

        // look for declaration in this and previous switch entry statements
        for (SwitchEntry seStmt : switchStmt.getEntries()) {
            for (Statement stmt : seStmt.getStatements()) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(stmt, typeSolver);
                SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
                if (symbolReference.isSolved()) {
                    return symbolReference;
                }
            }
            // once we reach this switch entry statement, stop: we do not want to look in later switch entry statements
            if (seStmt == wrappedNode) {
                break;
            }
        }

        return getParent().solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }
}
