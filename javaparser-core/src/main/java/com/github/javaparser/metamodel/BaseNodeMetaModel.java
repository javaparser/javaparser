package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.decapitalize;

/**
 * Meta-data about all classes in the AST. These are all Nodes, except NodeList.
 */
public abstract class BaseNodeMetaModel {
    private final Optional<BaseNodeMetaModel> superNodeMetaModel;
    private final List<PropertyMetaModel> declaredPropertyMetaModels = new ArrayList<>();
    private final List<PropertyMetaModel> derivedPropertyMetaModels = new ArrayList<>();
    private final List<PropertyMetaModel> constructorParameters = new ArrayList<>();
    private final Class<? extends Node> type;
    private final String name;
    private final String packageName;
    private final boolean isAbstract;
    private final boolean hasWildcard;

    public BaseNodeMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {
        this.superNodeMetaModel = superNodeMetaModel;
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
     * @return a list of all properties declared directly in this node (not its parent nodes.) These are also available
     * as fields.
     */
    public List<PropertyMetaModel> getDeclaredPropertyMetaModels() {
        return declaredPropertyMetaModels;
    }

    public List<PropertyMetaModel> getDerivedPropertyMetaModels() {
        return derivedPropertyMetaModels;
    }

    /**
     * @return a list of all properties that describe the parameters to the all-fields (but not "range" and "comment")
     * constructor, in the order of appearance in the constructor parameter list.
     */
    public List<PropertyMetaModel> getConstructorParameters() {
        return constructorParameters;
    }

    /**
     * @return a list of all properties in this node and its parents. Note that a new list is created every time this
     * method is called.
     */
    public List<PropertyMetaModel> getAllPropertyMetaModels() {
        List<PropertyMetaModel> allPropertyMetaModels = new ArrayList<>(getDeclaredPropertyMetaModels());
        BaseNodeMetaModel walkNode = this;
        while (walkNode.getSuperNodeMetaModel().isPresent()) {
            walkNode = walkNode.getSuperNodeMetaModel().get();
            allPropertyMetaModels.addAll(walkNode.getDeclaredPropertyMetaModels());
        }
        return allPropertyMetaModels;
    }

    public boolean isInstanceOfMetaModel(BaseNodeMetaModel baseMetaModel) {
        if (this == baseMetaModel) {
            return true;
        }
        if (isRootNode()) {
            return false;
        }
        return getSuperNodeMetaModel().get().isInstanceOfMetaModel(baseMetaModel);
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

    /**
     * @return whether this AST node is the root node, meaning that it is the meta model for "Node": "NodeMetaModel".
     */
    public boolean isRootNode() {
        return !superNodeMetaModel.isPresent();
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

    /**
     * The name of the field in JavaParserMetaModel for this node meta model.
     */
    public String getMetaModelFieldName() {
        return decapitalize(getClass().getSimpleName());
    }
}
