/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * <p>
 *     Required to prevent recursive access to the "parent node" (not necessarily the same as the "parent context").
 * </p><p>
 *     Consider, for example, this code where the cursor is currently at the node of type {@code ArrayAccessExpr}:
 * </p>
 * <pre>{@code
 *     var1.perPriority[index].recovered
 *     ^^^^^^^^^^^^^^^^^^^^^^^             - ArrayAccessExpr
 * }</pre>
 *
 * <p><b>The AST for this snippet:</b></p>
 *
 * <pre>{@code
 *                            FieldAccessExpr                       // This FieldAccessExpr is accessing the field `recovered`
 *                             /           \
 *               **ArrayAccessExpr**      SimpleName(recovered)
 *                  /          \
 *          FieldAccessExpr  NameExpr(index)                        // This FieldAccessExpr is accessing the field `perPriority`
 *            /         \
 *    NameExpr(var1)   SimpleName (perPriority)
 * }</pre>
 *
 * <p><b>In this example:</b></p>
 * <ul>
 *     <li>
 *         The parent node for {@code ArrayAccessExpr} is {@code FieldAccessExpr} ({@code variable1.perPriority[index].recovered}).
 * <pre>{@code
 *     // "Parent Node" of the ArrayAccessExpr
 *     var.perPriority[index].recovered
 *     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^   - FieldAccessExpr
 *     ^^^^^^^^^^^^^^^^^^^^^^             - ArrayAccessExpr
 *                            ^^^^^^^^^   - SimpleName
 * }</pre>
 *     </li>
 *     <li>
 *         The parent context is the {@code FieldAccessExpr} to the left of the outer array-access, which is actually a child node.
 * <pre>{@code
 *
 *     // "Parent Context" of the ArrayAccessExpr
 *     var1.perPriority[index].recovered
 *     ^^^^^^^^^^^^^^^^^^^^^^^             - ArrayAccessExpr
 *     ^^^^^^^^^^^^^^^^                    - FieldAccessExpr
 *                      ^^^^^              - NameExpr
 * }</pre>
 *     </li>
 * </ul>
 *
 *
 *
 *
 * @author Roger Howell
 */
public class ArrayAccessExprContext extends AbstractJavaParserContext<ArrayAccessExpr> {

    public ArrayAccessExprContext(ArrayAccessExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInParentContext(String name) {
        /*
         * Simple implementation, included explicitly here for clarity:
         * - Delegate to parent context per the documentation for ArrayAccessExprContext
         * - Required to prevent recursive access to the "parent node" (not necessarily the same as the "parent context")
         */
        return super.solveSymbolInParentContext(name);
    }

}
