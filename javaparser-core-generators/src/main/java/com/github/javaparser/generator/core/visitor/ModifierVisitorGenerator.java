package com.github.javaparser.generator.core.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.generator.VisitorGenerator;
import com.github.javaparser.generator.utils.SeparatedItemStringBuilder;
import com.github.javaparser.generator.utils.SourceRoot;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;

import static com.github.javaparser.generator.utils.GeneratorUtils.f;

/**
 * Generates JavaParser's EqualsVisitor.
 */
public class ModifierVisitorGenerator extends VisitorGenerator {
    public ModifierVisitorGenerator(JavaParser javaParser, SourceRoot sourceRoot) {
        super(javaParser, sourceRoot, "com.github.javaparser.ast.visitor", "ModifierVisitor", "Visitable", "A", true);
    }

    @Override
    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod, CompilationUnit compilationUnit) {
        BlockStmt body = visitMethod.getBody().get();
        body.getStatements().clear();

        String s1 = "Expression target = (Expression) n.getTarget().accept(this, arg);" +
                "        if (target == null) return null;" +
                "        n.setTarget(target);";

        String s = "n.setExtendedTypes(modifyList(n.getExtendedTypes(), arg));";
        String s2 = "n.getPackageDeclaration().ifPresent(p -> n.setPackageDeclaration((PackageDeclaration) p.accept(this, arg)));";


        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isNodeList()) {
                    body.addStatement(f("NodeList<%s> %s = modifyList(n.%s().orElse(null), arg);", field.getTypeNameGenerified(), field.getName(), getter));
                } else {
                    body.addStatement(f("%s %s = (Expression) n.getTarget().accept(this, arg);", field.getTypeNameGenerified(), field.getName(), getter));
                }
            }
        }

        SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder(f("%s r = new %s(", node.getTypeNameGenerified(), node.getTypeNameGenerified()), ",", ");");
        builder.append("_n.getRange().orElse(null)");
        for (PropertyMetaModel field : node.getConstructorParameters()) {
            if (field.getName().equals("comment")) {
                continue;
            }
            if (field.getNodeReference().isPresent()) {
                builder.append(field.getName());
            } else {
                builder.append(f("_n.%s()", field.getGetterMethodName()));
            }
        }

        body.addStatement(builder.toString());
        body.addStatement("r.setComment(comment);");
        body.addStatement("return r;");
    }
}

// TODO FieldDeclaration.variables may not be empty
// TODO BinaryExpr if left==null return right, etc.
// TODO VariableDeclarationExpr.variables may not be empty