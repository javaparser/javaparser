package com.github.jmlparser.redux;

import com.github.javaparser.Position;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.utils.Pair;
import com.github.jmlparser.utils.Helper;
import org.jetbrains.annotations.Nullable;

import java.util.HashSet;
import java.util.Set;

/**
 * Replaces lambda expression by an internal named class.
 * <p>
 * Code was donated by Carsten Czisky @ciskar
 */
public class LambdaReplacer implements Transformer {
    private final NameGenerator nameGenerator;

    public LambdaReplacer(NameGenerator nameGenerator) {
        this.nameGenerator = nameGenerator;
    }


    @Override
    public Node apply(Node a) {
        return Helper.findAndApply(LambdaExpr.class, a, this::rewriteLambda);
    }

    private <T extends Node> Node rewriteLambda(LambdaExpr expr) {
        var enclosingType = expr.getParentNodeOfType(TypeDeclaration.class);
        if (enclosingType.isEmpty())
            throw new IllegalStateException("LambdaExpr is not enclosed in a type declaration");
        ClassOrInterfaceDeclaration decl = liftToInnerClass(expr);
        enclosingType.get().addMember(decl);
        return instantiate(decl);
    }


    private ObjectCreationExpr instantiate(ClassOrInterfaceDeclaration decl) {
        var type = new ClassOrInterfaceType(null, decl.getNameAsString());
        return new ObjectCreationExpr(null, type, new NodeList());
    }

    private ClassOrInterfaceDeclaration liftToInnerClass(LambdaExpr lambdaExpr) {
        var sai = findSingleAbstractInterface(lambdaExpr);
        var interfazeName = sai.a;
        var method = sai.b;
        var name = nameGenerator.generate("__GENERATED_", lambdaExpr.getRange().orElse(null).begin);
        var it = new ClassOrInterfaceDeclaration(new NodeList(), false, name);
        it.addImplementedType(interfazeName);
        it.addMember(method);
        return it;
    }

    private Pair<String, MethodDeclaration> findSingleAbstractInterface(LambdaExpr lambdaExpr) {
        @Nullable ClassOrInterfaceType type = assignToType(lambdaExpr);
        if (type == null) {
            return inferDefaultAbstractInterface(lambdaExpr);
        } else {
            return new Pair<>(type.getNameAsString(), new MethodDeclaration());
        }
    }

    private Pair<String, MethodDeclaration> inferDefaultAbstractInterface(LambdaExpr lambdaExpr) {
        var interfaze = "";
        var md = new MethodDeclaration();

        var body = lambdaExpr.getBody();
        String returnType = null;

        if (body instanceof BlockStmt bs) {
            var last = bs.getStatements().getLast();
            returnType = last.flatMap(it -> it.asReturnStmt().getExpression())
                    .map(b -> b.calculateResolvedType().toString()).orElse(null);
        }

        if (body instanceof ExpressionStmt es) {
            returnType = es.getExpression().calculateResolvedType().toString();
        }


        switch (lambdaExpr.getParameters().size()) {
            case 0 -> {
                if (returnType == null) {
                    interfaze = "Runnable";
                    md.setName("run");
                } else {
                    interfaze = "java.util.function.Supplier<$returnType>";
                    md.setName("accept");
                }
            }
            case 1 -> {
                var firstParam = lambdaExpr.getParameters().getFirst().get().getTypeAsString();
                if (returnType == null) {
                    interfaze = "java.util.function.Consumer<" + firstParam + ">";
                    md.setName("get");
                } else {
                    interfaze = "java.util.function.Function<" + firstParam + ", " + returnType + ">";
                    md.setName("invoke");
                }
            }

            case 2 -> {
                var firstParam = lambdaExpr.getParameters().getFirst().map(Parameter::getTypeAsString).orElse(null);
                var secondParam = lambdaExpr.getParameters().get(1).getTypeAsString();
                if (returnType == null) {
                    interfaze = "java.util.function.Consumer<" + firstParam + ">";
                    md.setName("get");
                } else {
                    interfaze = "java.util.function.BiFunction<$firstParam, $secondParam, $returnType>";
                    md.setName("invoke");
                }
            }
            default -> throw new IllegalStateException("ASM could not be infered");
        }
        //TODO md.type = returnType
        for (var parameter : lambdaExpr.getParameters()) {
            md.addParameter(parameter.clone());
        }
        return new Pair<>(interfaze, md);
    }

    @Nullable
    private ClassOrInterfaceType assignToType(LambdaExpr lambdaExpr) {
        var type = lambdaExpr.calculateResolvedType();
        System.out.println("TEST: $type");
        return null; //TODO
    }
}

/**
 * generates names guaranteeing uniqueness in generated names by onw instance of NameGenerator
 */
class NameGenerator {
    private Set<String> generatedNames = new HashSet<>();

    public String generate(String prefix, @Nullable Position pos) {
        return generate(prefix, pos, null);
    }

    private String generate(String prefix, @Nullable Position pos, Integer counter) {
        var line = pos != null ? pos.line : null;
        var newName = prefix + "L" + line;
        if (counter != null) {
            newName += "_" + counter;
        }
        if (generatedNames.contains(newName)) {
            return generate(prefix, pos, counter != null ? counter + 1 : 0);
        }
        generatedNames.add(newName);
        return newName;
    }
}
