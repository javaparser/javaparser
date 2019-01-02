package com.github.javaparser.ast.modules;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import java.util.Optional;
import com.github.javaparser.metamodel.ModuleDirectiveMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A module directive.
 */
public abstract class ModuleDirective extends Node {

    @AllFieldsConstructor
    public ModuleDirective() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleDirective(TokenRange tokenRange) {
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
    public ModuleDirective clone() {
        return (ModuleDirective) accept(new CloneVisitor(), null);
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
    public ModuleExportsDirective asModuleExportsStmt() {
        throw new IllegalStateException(f("%s is not an ModuleExportsDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleOpensStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleOpensDirective asModuleOpensStmt() {
        throw new IllegalStateException(f("%s is not an ModuleOpensDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleProvidesStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleProvidesDirective asModuleProvidesStmt() {
        throw new IllegalStateException(f("%s is not an ModuleProvidesDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleRequiresStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleRequiresDirective asModuleRequiresStmt() {
        throw new IllegalStateException(f("%s is not an ModuleRequiresDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesStmt() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesDirective asModuleUsesStmt() {
        throw new IllegalStateException(f("%s is not an ModuleUsesDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleExportsStmt(Consumer<ModuleExportsDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleOpensStmt(Consumer<ModuleOpensDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleProvidesStmt(Consumer<ModuleProvidesDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleRequiresStmt(Consumer<ModuleRequiresDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesStmt(Consumer<ModuleUsesDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleExportsDirective> toModuleExportsStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleOpensDirective> toModuleOpensStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleProvidesDirective> toModuleProvidesStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleRequiresDirective> toModuleRequiresStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleUsesDirective> toModuleUsesStmt() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleExportsDirective() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleExportsDirective asModuleExportsDirective() {
        throw new IllegalStateException(f("%s is not an ModuleExportsDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleExportsDirective> toModuleExportsDirective() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleExportsDirective(Consumer<ModuleExportsDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleOpensDirective() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleOpensDirective asModuleOpensDirective() {
        throw new IllegalStateException(f("%s is not an ModuleOpensDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleOpensDirective> toModuleOpensDirective() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleOpensDirective(Consumer<ModuleOpensDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleProvidesDirective() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleProvidesDirective asModuleProvidesDirective() {
        throw new IllegalStateException(f("%s is not an ModuleProvidesDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleProvidesDirective> toModuleProvidesDirective() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleProvidesDirective(Consumer<ModuleProvidesDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleRequiresDirective() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleRequiresDirective asModuleRequiresDirective() {
        throw new IllegalStateException(f("%s is not an ModuleRequiresDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleRequiresDirective> toModuleRequiresDirective() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleRequiresDirective(Consumer<ModuleRequiresDirective> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isModuleUsesDirective() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ModuleUsesDirective asModuleUsesDirective() {
        throw new IllegalStateException(f("%s is not an ModuleUsesDirective", this));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ModuleUsesDirective> toModuleUsesDirective() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifModuleUsesDirective(Consumer<ModuleUsesDirective> action) {
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleDirectiveMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleDirectiveMetaModel;
    }
}
