package com.github.javaparser.ast.validator.chunks;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleRequiresDirective;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.javaparser.utils.SeparatedItemStringBuilder;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.ast.Modifier.Keyword.*;
import static java.util.Arrays.asList;


/**
 * Verifies that only allowed modifiers are used where modifiers are expected.
 */
public class ModifierValidator extends VisitorValidator {
    private final Modifier.Keyword[] interfaceWithNothingSpecial = new Modifier.Keyword[]{PUBLIC, PROTECTED, ABSTRACT, FINAL, SYNCHRONIZED, NATIVE, STRICTFP};
    private final Modifier.Keyword[] interfaceWithStaticAndDefault = new Modifier.Keyword[]{PUBLIC, PROTECTED, ABSTRACT, STATIC, FINAL, SYNCHRONIZED, NATIVE, STRICTFP, DEFAULT};
    private final Modifier.Keyword[] interfaceWithStaticAndDefaultAndPrivate = new Modifier.Keyword[]{PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, FINAL, SYNCHRONIZED, NATIVE, STRICTFP, DEFAULT};

    private final boolean hasStrictfp;
    private final boolean hasDefaultAndStaticInterfaceMethods;
    private final boolean hasPrivateInterfaceMethods;

    public ModifierValidator(boolean hasStrictfp, boolean hasDefaultAndStaticInterfaceMethods, boolean hasPrivateInterfaceMethods) {
        this.hasStrictfp = hasStrictfp;
        this.hasDefaultAndStaticInterfaceMethods = hasDefaultAndStaticInterfaceMethods;
        this.hasPrivateInterfaceMethods = hasPrivateInterfaceMethods;
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
        if (n.isInterface()) {
            validateInterfaceModifiers(n, reporter);
        } else {
            validateClassModifiers(n, reporter);
        }
        super.visit(n, reporter);
    }

    private void validateClassModifiers(ClassOrInterfaceDeclaration n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, ABSTRACT, FINAL, STRICTFP);
        } else if (n.isNestedType()) {
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, FINAL, STRICTFP);
        } else if (n.isLocalClassDeclaration()) {
            validateModifiers(n, reporter, ABSTRACT, FINAL, STRICTFP);
        }
    }

    private void validateInterfaceModifiers(TypeDeclaration<?> n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, ABSTRACT, STRICTFP);
        } else if (n.isNestedType()) {
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, STRICTFP);
        }
    }

    @Override
    public void visit(EnumDeclaration n, ProblemReporter reporter) {
        if (n.isTopLevelType()) {
            validateModifiers(n, reporter, PUBLIC, STRICTFP);
        } else if (n.isNestedType()) {
            validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, STATIC, STRICTFP);
        }
        super.visit(n, reporter);
    }

    @Override
    public void visit(AnnotationDeclaration n, ProblemReporter reporter) {
        validateInterfaceModifiers(n, reporter);
        super.visit(n, reporter);
    }

    @Override
    public void visit(AnnotationMemberDeclaration n, ProblemReporter reporter) {
        validateModifiers(n, reporter, PUBLIC, ABSTRACT);
        super.visit(n, reporter);
    }

    @Override
    public void visit(ConstructorDeclaration n, ProblemReporter reporter) {
        validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE);
        n.getParameters().forEach(p -> validateModifiers(p, reporter, FINAL));
        super.visit(n, reporter);
    }

    @Override
    public void visit(FieldDeclaration n, ProblemReporter reporter) {
        validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, STATIC, FINAL, TRANSIENT, VOLATILE);
        super.visit(n, reporter);
    }

    @Override
    public void visit(MethodDeclaration n, ProblemReporter reporter) {
        if (n.isAbstract()) {
            final SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder("Cannot be 'abstract' and also '", "', '", "'.");
            for (Modifier.Keyword m : asList(PRIVATE, STATIC, FINAL, NATIVE, STRICTFP, SYNCHRONIZED)) {
                if (n.hasModifier(m)) {
                    builder.append(m.asString());
                }
            }
            if (builder.hasItems()) {
                reporter.report(n, builder.toString());
            }
        }
        if (n.getParentNode().isPresent()) {
            if (n.getParentNode().get() instanceof ClassOrInterfaceDeclaration) {
                if (((ClassOrInterfaceDeclaration) n.getParentNode().get()).isInterface()) {
                    if (hasDefaultAndStaticInterfaceMethods) {
                        if (hasPrivateInterfaceMethods) {
                            validateModifiers(n, reporter, interfaceWithStaticAndDefaultAndPrivate);
                        } else {
                            validateModifiers(n, reporter, interfaceWithStaticAndDefault);
                        }
                    } else {
                        validateModifiers(n, reporter, interfaceWithNothingSpecial);
                    }
                } else {
                    validateModifiers(n, reporter, PUBLIC, PROTECTED, PRIVATE, ABSTRACT, STATIC, FINAL, SYNCHRONIZED, NATIVE, STRICTFP);
                }
            }
        }
        n.getParameters().forEach(p -> validateModifiers(p, reporter, FINAL));
        super.visit(n, reporter);
    }

    @Override
    public void visit(LambdaExpr n, ProblemReporter reporter) {
        n.getParameters().forEach(p -> {
            // Final is not allowed on inferred parameters, but those get caught by the parser.
            validateModifiers(p, reporter, FINAL);
        });
        super.visit(n, reporter);
    }

    @Override
    public void visit(CatchClause n, ProblemReporter reporter) {
        validateModifiers(n.getParameter(), reporter, FINAL);
        super.visit(n, reporter);
    }

    @Override
    public void visit(VariableDeclarationExpr n, ProblemReporter reporter) {
        validateModifiers(n, reporter, FINAL);
        super.visit(n, reporter);
    }

    @Override
    public void visit(ModuleRequiresDirective n, ProblemReporter reporter) {
        validateModifiers(n, reporter, TRANSITIVE, STATIC);
        super.visit(n, reporter);
    }

    private <T extends NodeWithModifiers<?> & NodeWithTokenRange<?>> void validateModifiers(T n, ProblemReporter reporter, Modifier.Keyword... allowedModifiers) {
        validateAtMostOneOf(n, reporter, PUBLIC, PROTECTED, PRIVATE);
        validateAtMostOneOf(n, reporter, FINAL, ABSTRACT);
        if (hasStrictfp) {
            validateAtMostOneOf(n, reporter, NATIVE, STRICTFP);
        } else {
            allowedModifiers = removeModifierFromArray(STRICTFP, allowedModifiers);
        }
        for (Modifier m : n.getModifiers()) {
            if (!arrayContains(allowedModifiers, m.getKeyword())) {
                reporter.report(n, "'%s' is not allowed here.", m.getKeyword().asString());
            }
        }
    }

    private Modifier.Keyword[] removeModifierFromArray(Modifier.Keyword m, Modifier.Keyword[] allowedModifiers) {
        final List<Modifier.Keyword> newModifiers = new ArrayList<>(asList(allowedModifiers));
        newModifiers.remove(m);
        allowedModifiers = newModifiers.toArray(new Modifier.Keyword[0]);
        return allowedModifiers;
    }

    private boolean arrayContains(Object[] items, Object searchItem) {
        for (Object o : items) {
            if (o == searchItem) {
                return true;
            }
        }
        return false;
    }

    private <T extends NodeWithModifiers<?> & NodeWithTokenRange<?>> void validateAtMostOneOf(T t, ProblemReporter reporter, Modifier.Keyword... modifiers) {
        List<Modifier.Keyword> foundModifiers = new ArrayList<>();
        for (Modifier.Keyword m : modifiers) {
            if (t.hasModifier(m)) {
                foundModifiers.add(m);
            }
        }
        if (foundModifiers.size() > 1) {
            SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder("Can have only one of '", "', '", "'.");
            for (Modifier.Keyword m : foundModifiers) {
                builder.append(m.asString());
            }
            reporter.report(t, builder.toString());
        }
    }

}
