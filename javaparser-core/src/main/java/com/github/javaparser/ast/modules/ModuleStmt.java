package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleStmtMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;

public abstract class ModuleStmt extends Node {

    @AllFieldsConstructor
    public ModuleStmt() {
        this(null);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleStmt(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ModuleStmt clone() {
        return (ModuleStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleExportsStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleExportsStmt asModuleExportsStmt() {
        return (ModuleExportsStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleOpensStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleOpensStmt asModuleOpensStmt() {
        return (ModuleOpensStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleProvidesStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleProvidesStmt asModuleProvidesStmt() {
        return (ModuleProvidesStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleRequiresStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleRequiresStmt asModuleRequiresStmt() {
        return (ModuleRequiresStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesStmt asModuleUsesStmt() {
        return (ModuleUsesStmt) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleExportsStmt(Consumer<ModuleExportsStmt> action) {
        if (isModuleExportsStmt()) {
            action.accept(asModuleExportsStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleOpensStmt(Consumer<ModuleOpensStmt> action) {
        if (isModuleOpensStmt()) {
            action.accept(asModuleOpensStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleProvidesStmt(Consumer<ModuleProvidesStmt> action) {
        if (isModuleProvidesStmt()) {
            action.accept(asModuleProvidesStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleRequiresStmt(Consumer<ModuleRequiresStmt> action) {
        if (isModuleRequiresStmt()) {
            action.accept(asModuleRequiresStmt());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesStmt(Consumer<ModuleUsesStmt> action) {
        if (isModuleUsesStmt()) {
            action.accept(asModuleUsesStmt());
        }
    }
}
