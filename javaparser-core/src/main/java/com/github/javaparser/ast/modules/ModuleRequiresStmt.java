package com.github.javaparser.ast.modules;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleRequiresStmtMetaModel;
import java.util.EnumSet;
import static com.github.javaparser.ast.Modifier.TRANSITIVE;
import static com.github.javaparser.utils.Utils.assertNotNull;
import javax.annotation.Generated;

/**
 * A require statement in module-info.java. <code>require a.b.C;</code>
 */
public class ModuleRequiresStmt extends ModuleStmt implements NodeWithStaticModifier<ModuleRequiresStmt>, NodeWithName<ModuleRequiresStmt> {

    private EnumSet<Modifier> modifiers;

    private Name name;

    public ModuleRequiresStmt() {
        this(null, EnumSet.noneOf(Modifier.class), new Name());
    }

    @AllFieldsConstructor
    public ModuleRequiresStmt(EnumSet<Modifier> modifiers, Name name) {
        this(null, modifiers, name);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ModuleRequiresStmt(Range range, EnumSet<Modifier> modifiers, Name name) {
        super(range);
        setModifiers(modifiers);
        setName(name);
        customInitialization();
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleRequiresStmt setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return (ModuleRequiresStmt) this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ModuleRequiresStmt setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ModuleRequiresStmt) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    public boolean isTransitive() {
        return getModifiers().contains(TRANSITIVE);
    }

    public ModuleRequiresStmt setTransitive(boolean set) {
        return setModifier(TRANSITIVE, set);
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
    public ModuleRequiresStmt clone() {
        return (ModuleRequiresStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ModuleRequiresStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleRequiresStmtMetaModel;
    }
}
