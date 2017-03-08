package com.github.javaparser.ast.modules;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ModuleOpensStmtMetaModel;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;

public class ModuleOpensStmt extends ModuleStmt implements NodeWithName<ModuleOpensStmt> {

    private Name name;

    private NodeList<Name> moduleNames;

    public ModuleOpensStmt() {
        this(null, new Name(), new NodeList<>());
    }

    @AllFieldsConstructor
    public ModuleOpensStmt(Name name, NodeList<Name> moduleNames) {
        this(null, name, moduleNames);
    }

    public ModuleOpensStmt(Range range, Name name, NodeList<Name> moduleNames) {
        super(range);
        setName(name);
        setModuleNames(moduleNames);
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
        for (int i = 0; i < moduleNames.size(); i++) {
            if (moduleNames.get(i) == node) {
                moduleNames.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    public Name getName() {
        return name;
    }

    public ModuleOpensStmt setName(final Name name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    public NodeList<Name> getModuleNames() {
        return moduleNames;
    }

    public ModuleOpensStmt setModuleNames(final NodeList<Name> moduleNames) {
        assertNotNull(moduleNames);
        notifyPropertyChange(ObservableProperty.MODULE_NAMES, this.moduleNames, moduleNames);
        if (this.moduleNames != null)
            this.moduleNames.setParentNode(null);
        this.moduleNames = moduleNames;
        setAsParentNodeOf(moduleNames);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getModuleNames());
    }

    @Override
    public ModuleOpensStmt clone() {
        return (ModuleOpensStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ModuleOpensStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.moduleOpensStmtMetaModel;
    }
}
