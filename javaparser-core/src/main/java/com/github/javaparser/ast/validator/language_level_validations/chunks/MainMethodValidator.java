/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;

/**
 * Validator for JEP 512: Flexible Main Method Signatures.
 *
 * Validates main method signatures according to JEP 512:
 * - Main can be static or instance
 * - Main can be public or package-private
 * - Main can return void or int
 * - Main can have String[] parameter or no parameters
 * - Main can have varargs String...
 *
 * @see <a href="https://openjdk.org/jeps/512">JEP 512</a>
 */
public class MainMethodValidator implements TypedValidator<MethodDeclaration> {

    @Override
    public void accept(MethodDeclaration node, ProblemReporter reporter) {
        validateMainMethodSignature(node, reporter);
    }

    /**
     * Validates that a main method has a valid signature according to JEP 512.
     *
     * Valid signatures:
     * - void main()
     * - void main(String[] args)
     * - int main()
     * - int main(String[] args)
     * - static void main(String[] args)  [classic]
     * - public static void main(String[] args)  [classic]
     * - public void main()  [new in JEP 512]
     * - public void main(String[] args)  [new in JEP 512]
     */
    private void validateMainMethodSignature(MethodDeclaration method, ProblemReporter reporter) {
        // Only validate methods named "main"
        if (!method.getNameAsString().equals("main")) {
            return;
        }

        // Check return type (must be void or int)
        String returnType = method.getTypeAsString();
        if (!returnType.equals("void") && !returnType.equals("int")) {
            reporter.report(
                    method,
                    String.format("Main method must have return type 'void' or 'int', found: '%s'.", returnType));
            return;
        }
        // Check parameters (must be empty or String[])
        int paramCount = method.getParameters().size();
        if (paramCount == 0) {
            // Valid: void main() or int main()
            return;
        } else if (paramCount == 1) {
            // Must be String[] or String...
            String paramType = method.getParameter(0).getTypeAsString();
            // Handle varargs
            String paramTypeCleaned = paramType.replace("...", "[]");
            if (!paramTypeCleaned.equals("String[]")) {
                reporter.report(
                        method, String.format("Main method parameter must be 'String[]', found: '%s'.", paramType));
            }
        } else {
            // More than 1 parameter is invalid
            reporter.report(method, "Main method must have zero or one parameter (String[]).");
        }
    }
}