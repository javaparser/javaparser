/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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
package com.github.javaparser.ast.validator.language_level_validations.chunks;

import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;

public class SwitchExprValidator implements TypedValidator<SwitchExpr> {

    @Override
    public void accept(SwitchExpr node, ProblemReporter reporter) {
        validateHasResultExpressions(node, reporter);
    }

    /**
     * "It is a compile-time error if a switch expression has no result expressions." (JLS 15.28.1)
     * A result expression is a non-throwing switch rule - if all switch rules throw,
     * there are no result expressions.
     */
    private void validateHasResultExpressions(SwitchExpr n, ProblemReporter reporter) {
        boolean allThrow =
                n.getEntries().stream().allMatch(entry -> entry.getType() == SwitchEntry.Type.THROWS_STATEMENT);
        if (allThrow) {
            reporter.report(n, "Switch expression does not have any result expressions.");
        }
    }
}
