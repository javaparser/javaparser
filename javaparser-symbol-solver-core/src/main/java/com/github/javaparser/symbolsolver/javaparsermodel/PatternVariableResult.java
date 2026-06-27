/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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
package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.expr.TypePatternExpr;
import java.util.LinkedList;
import java.util.List;

public class PatternVariableResult {
    private List<TypePatternExpr> variablesIntroducedIfTrue;
    private List<TypePatternExpr> variablesIntroducedIfFalse;

    public PatternVariableResult(
            LinkedList<TypePatternExpr> variablesIntroducedIfTrue,
            LinkedList<TypePatternExpr> variablesIntroducedIfFalse) {
        this.variablesIntroducedIfTrue = variablesIntroducedIfTrue;
        this.variablesIntroducedIfFalse = variablesIntroducedIfFalse;
    }

    public PatternVariableResult() {
        variablesIntroducedIfTrue = new LinkedList<>();
        variablesIntroducedIfFalse = new LinkedList<>();
    }

    public List<TypePatternExpr> getVariablesIntroducedIfTrue() {
        return variablesIntroducedIfTrue;
    }

    public List<TypePatternExpr> getVariablesIntroducedIfFalse() {
        return variablesIntroducedIfFalse;
    }

    public void addVariablesIntroducedIfTrue(List<TypePatternExpr> patterns) {
        variablesIntroducedIfTrue.addAll(patterns);
    }

    public void addVariablesIntroducedIfFalse(List<TypePatternExpr> patterns) {
        variablesIntroducedIfFalse.addAll(patterns);
    }

    public void clearVariablesIntroducedIfTrue() {
        variablesIntroducedIfTrue.clear();
    }

    public void clearVariablesIntroducedIfFalse() {
        variablesIntroducedIfFalse.clear();
    }

    public void swapTrueAndFalse() {
        List<TypePatternExpr> temp = variablesIntroducedIfTrue;
        variablesIntroducedIfTrue = variablesIntroducedIfFalse;
        variablesIntroducedIfFalse = temp;
    }
}
