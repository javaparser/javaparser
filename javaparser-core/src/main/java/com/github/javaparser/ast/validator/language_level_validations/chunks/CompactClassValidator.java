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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;

/**
 * Validator for JEP 512: Compact Source Files and Instance Main Methods.
 *
 * Validates compact class restrictions:
 * - Compact classes cannot extend other classes
 * - Compact classes cannot implement interfaces
 * - Compact classes are implicitly final
 *
 * Validates flexible main method signatures (allowed in Java 25):
 * - Main can be static or instance
 * - Main can be public or package-private
 * - Main can return void or int
 * - Main can have String[] parameter or no parameters
 *
 * @see <a href="https://openjdk.org/jeps/512">JEP 512</a>
 */
public class CompactClassValidator implements TypedValidator<ClassOrInterfaceDeclaration> {

    @Override
    public void accept(ClassOrInterfaceDeclaration node, ProblemReporter reporter) {
        // Validate compact class restrictions (only for compact classes)
        if (node.isCompact()) {
            validateCompactClassRestrictions(node, reporter);
        }
        
        // Validate main methods (for ALL classes, not just compact)
        validateMainMethods(node, reporter);
    }

    /**
     * Compact classes have restrictions according to JEP 512:
     * - Cannot extend other classes
     * - Cannot implement interfaces
     * - Are implicitly final
     */
    private void validateCompactClassRestrictions(ClassOrInterfaceDeclaration node, ProblemReporter reporter) {
        // Check for extends clause
        if (!node.getExtendedTypes().isEmpty()) {
            reporter.report(node, "Compact classes cannot extend other classes.");
        }
        // Check for implements clause
        if (!node.getImplementedTypes().isEmpty()) {
            reporter.report(node, "Compact classes cannot implement interfaces.");
        }
        // Check for explicit abstract modifier (compact classes are implicitly final)
        if (node.getModifiers().contains(Modifier.abstractModifier())) {
            reporter.report(node, "Compact classes cannot be declared as abstract.");
        }
    }

    /**
     * Validates main methods in compact classes.
     * JEP 512 allows flexible main method signatures:
     * - Can be static or instance
     * - Can be public or package-private
     * - Can return void or int
     * - Can have String[] parameter or no parameters
     */
    private void validateMainMethods(ClassOrInterfaceDeclaration node, ProblemReporter reporter) {
        node.getMethodsByName("main").forEach(method -> {
            validateMainMethodSignature(method, reporter);
        });
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
