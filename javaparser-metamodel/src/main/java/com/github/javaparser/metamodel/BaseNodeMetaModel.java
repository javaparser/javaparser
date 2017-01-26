package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Meta-data about all classes in the AST.
 * These are all Nodes, except NodeList.
 */
public abstract class BaseNodeMetaModel {
    private final Optional<BaseNodeMetaModel> superNodeMetaModel;
    private final JavaParserMetaModel javaParserMetaModel;
    private final List<PropertyMetaModel> propertyMetaModels = new ArrayList<>();
    private final Class<? extends Node> type;
    private final String name;
    private final String packageName;
    private final boolean isAbstract;
    private final boolean hasWildcard;

    public BaseNodeMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, JavaParserMetaModel javaParserMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {
        this.superNodeMetaModel = superNodeMetaModel;
        this.javaParserMetaModel = javaParserMetaModel;
        this.type = type;
        this.name = name;
        this.packageName = packageName;
        this.isAbstract = isAbstract;
        this.hasWildcard = hasWildcard;
    }

    /**
     * @return is this the meta model for this node class?
     */
    public boolean is(Class<? extends Node> c) {
        return type.equals(c);
    }

    /**
     * @return package name + class name
     */
    public String getQualifiedClassName() {
        return packageName + "." + name;
    }

    /**
     * @return the meta model for the node that this node extends. Note that this is to be used to find properties
     * defined in superclasses of a Node.
     */
    public Optional<BaseNodeMetaModel> getSuperNodeMetaModel() {
        return superNodeMetaModel;
    }

    /**
     * @return the overall model.
     */
    public JavaParserMetaModel getJavaParserMetaModel() {
        return javaParserMetaModel;
    }

    /**
     * @return a list of all properties. These are also available as fields.
     */
    public List<PropertyMetaModel> getPropertyMetaModels() {
        return propertyMetaModels;
    }

    /**
     * @return the class for this AST node type.
     */
    public Class<? extends Node> getType() {
        return type;
    }

    /**
     * @return the package containing this AST node class.
     */
    public String getPackageName() {
        return packageName;
    }

    /**
     * @return whether this AST node is abstract.
     */
    public boolean isAbstract() {
        return isAbstract;
    }

    /**
     * @return whether this AST node has a &lt;?&gt; at the end of its type.
     */
    public boolean hasWildcard() {
        return hasWildcard;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BaseNodeMetaModel classMetaModel = (BaseNodeMetaModel) o;

        if (!type.equals(classMetaModel.type)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return type.hashCode();
    }

    @Override
    public String toString() {
        return name;
    }

    /**
     * @return the type name, with generics.
     */
    public String getTypeNameGenerified() {
        if (hasWildcard) {
            return getTypeName() + "<?>";
        }
        return getTypeName();
    }

    /**
     * @return the raw type name, so nothing but the name.
     */
    public String getTypeName() {
        return type.getSimpleName();
    }
}
