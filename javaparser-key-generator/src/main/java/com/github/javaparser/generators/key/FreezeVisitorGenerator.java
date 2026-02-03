package com.github.javaparser.generators.key;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.CompilationUnitMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.SeparatedItemStringBuilder;
import com.github.javaparser.utils.SourceRoot;

import java.nio.file.Path;

import static com.github.javaparser.StaticJavaParser.parseType;
import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class FreezeVisitorGenerator extends Generator {

    private final Path outputDirectory;

    public FreezeVisitorGenerator(SourceRoot sourceRoot, Path outputDirectory) {
        super(sourceRoot);
        this.outputDirectory = outputDirectory;
    }

    @Override
    public void generate() throws Exception {
        CompilationUnit cu = new CompilationUnit();
        cu.setPackageDeclaration(Transformers.PACKAGE_VISITORS_NEW);
        addImports(cu, Transformers.PACKAGE_NODE_OLD);
        addImports(cu, Transformers.PACKAGE_NODE_NEW);

        var type = cu.addClass("FreezeVisitor");
        type.getImplementedTypes()
                .add((ClassOrInterfaceType) parseType("GenericVisitor<INode,Void>"));
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            generateVisitMethodBody(type, nodeMetaModel);
        }
        Transformers.write(cu,type.getFullyQualifiedName().get(), outputDirectory);
    }

    private void generateVisitMethodBody(ClassOrInterfaceDeclaration type, BaseNodeMetaModel nodeMetaModel) {
        var method = type.addMethod("visit", Modifier.Keyword.PUBLIC);
        method.setType("I" + nodeMetaModel.getTypeName());
        method.addParameter(nodeMetaModel.getTypeName(), "n");
        method.addParameter(parseType("Void"), "arg");
        generateVisitMethodBody(nodeMetaModel, method);
    }

    protected void generateVisitMethodBody(BaseNodeMetaModel node, MethodDeclaration visitMethod) {
        visitMethod.getParameters().forEach(p -> p.setFinal(true));

        BlockStmt body = new BlockStmt();
        visitMethod.setBody(body);

        for (PropertyMetaModel field : node.getAllPropertyMetaModels()) {
            final String getter = field.getGetterMethodName() + "()";
            if (field.getNodeReference().isPresent()) {
                if (field.isOptional() && field.isNodeList()) {
                    body.addStatement(f("INodeList<%s> %s = cloneList(n.%s.orElse(null), arg);", field.getTypeNameGenerified(), field.getName(), getter));
                } else if (field.isNodeList()) {
                    body.addStatement(f("INodeList<%s> %s = cloneList(n.%s, arg);", field.getTypeNameGenerified(), field.getName(), getter));
                } else {
                    body.addStatement(f("I%s %s = cloneNode(n.%s, arg);", field.getTypeNameGenerified(), field.getName(), getter));
                }
            }
        }

        SeparatedItemStringBuilder builder = new SeparatedItemStringBuilder(f("I%s r = new I%s(", node.getTypeNameGenerified(), node.getTypeNameGenerified()), ",", ");");
        builder.append("n.getTokenRange().orElse(null)");
        for (PropertyMetaModel field : node.getConstructorParameters()) {
            if (field.getName().equals("comment")) {
                continue;
            }
            if (field.getNodeReference().isPresent()) {
                builder.append(field.getName());
            } else {
                builder.append(f("n.%s()", field.getGetterMethodName()));
            }
        }

        body.addStatement(builder.toString());
        if (node instanceof CompilationUnitMetaModel) {
            body.addStatement("n.getStorage().ifPresent(s -> r.setStorage(s.getPath(), s.getEncoding()));");
        }
        //body.addStatement("r.setComment(comment);");
        //body.addStatement("n.getOrphanComments().stream().map(Comment::clone).forEach(r::addOrphanComment);");
        //body.addStatement("copyData(n, r);");
        body.addStatement("return r;");
    }


    private void addImports(CompilationUnit cu, String p) {
        cu.addImport(p + ".body.*");
        cu.addImport(p + ".expr.*");
        cu.addImport(p + ".comments.*");
        cu.addImport(p + ".modules.*");
        cu.addImport(p + ".type.*");
        cu.addImport(p + ".stmt.*");
        cu.addImport(p + ".*");
    }
}
