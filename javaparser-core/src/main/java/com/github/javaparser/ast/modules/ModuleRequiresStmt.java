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

    public ModuleRequiresStmt(Range range, EnumSet<Modifier> modifiers, Name name) {
        super(range);
        setModifiers(modifiers);
        setName(name);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Override
    public ModuleRequiresStmt setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public Name getName() {
        return name;
    }

    @Override
    public ModuleRequiresStmt setName(final Name name) {
        assertNotNull(name);
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
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public ModuleRequiresStmt clone() {
        return (ModuleRequiresStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ModuleRequiresStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleRequiresStmtMetaModel;
    }
}
