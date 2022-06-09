package com.github.javaparser.ast.validator.language_level_validations.chunks;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;

public class RecordDeclarationValidator implements TypedValidator<RecordDeclaration> {

    @Override
    public void accept(RecordDeclaration node, ProblemReporter reporter) {
        forbidAbstractModifier(node, reporter);
        forbidNonStaticFieldsInRecords(node, reporter);
        validateRecordComponentAccessorMethods(node, reporter);
    }

    private void forbidAbstractModifier(RecordDeclaration n, ProblemReporter reporter) {
        if (n.getModifiers().contains(Modifier.abstractModifier())) {
            reporter.report(n, "Record Declarations must not be declared as abstract.");
        }
    }

    private void forbidNonStaticFieldsInRecords(RecordDeclaration n, ProblemReporter reporter) {
        long nonStaticFieldCount = n.getFields().stream()
                .filter(fieldDeclaration -> !fieldDeclaration.isStatic())
                .count();

        if (nonStaticFieldCount > 0) {
            reporter.report(n, "Record Declarations must have zero non-static fields.");
        }
    }

    /**
     * Given this sample record example:
     * <pre>{@code
     *     record ABC(int x, int y) { }
     * }</pre>
     * <p>
     * Permitted - shadows int x (matches name and return type)
     * <pre>{@code
     *     public int x() {
     *         return x;
     *     }
     * }</pre>
     * <p>
     * Forbidden - shadows int x, but has a type mismatch (String vs int).
     * <pre>{@code
     *     public String x() {
     *         return "";
     *     }
     * }</pre>
     * <p>
     * Permitted - shadows int x, but not considered a component accessor due to presence of parameter.
     * <pre>{@code
     *     public String x(int a) {
     *         return "";
     *     }
     * }</pre>
     */
    private void validateRecordComponentAccessorMethods(RecordDeclaration n, ProblemReporter reporter) {
        n.getParameters().forEach(parameter -> {
            n.getMethodsByName(parameter.getNameAsString())
                    .stream()
                    .filter(methodDeclaration -> methodDeclaration.getParameters().isEmpty())
                    .forEach(methodDeclaration -> {
                        if (!methodDeclaration.getType().equals(parameter.getType())) {
                            reporter.report(
                                    n,
                                    String.format(
                                            "Incorrect component accessor return type. Expected: '%s', found: '%s'.",
                                            parameter.getTypeAsString(),
                                            methodDeclaration.getTypeAsString()
                                    )
                            );
                        }
                    });
        });
    }
}
