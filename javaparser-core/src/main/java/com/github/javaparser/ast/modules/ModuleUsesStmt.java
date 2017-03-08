package com.github.javaparser.ast.modules;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleUsesStmtMetaModel;
import static com.github.javaparser.utils.Utils.assertNotNull;

public class ModuleUsesStmt extends ModuleStmt implements NodeWithType<ModuleUsesStmt, Type> {

    private Type type;

    public ModuleUsesStmt() {
        this(null);
    }

    @AllFieldsConstructor
    public ModuleUsesStmt(Type type) {
        this(null, type);
    }

    public ModuleUsesStmt(Range range, Type type) {
        super(range);
        setType(type);
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
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    public Type getType() {
        return type;
    }

    public ModuleUsesStmt setType(final Type type) {
        assertNotNull(type);
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    public ModuleUsesStmt clone() {
        return (ModuleUsesStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ModuleUsesStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleUsesStmtMetaModel;
    }
}
