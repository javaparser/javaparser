/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.Range;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.nodeTypes.NodeWithRange;
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import com.github.javaparser.ast.visitor.HashCodeVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.metamodel.*;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import static com.github.javaparser.ast.Node.Parsedness.PARSED;
import static com.github.javaparser.ast.Node.TreeTraversal.PREORDER;
import static java.util.Collections.emptySet;
import static java.util.Collections.unmodifiableList;
import static java.util.Spliterator.DISTINCT;
import static java.util.Spliterator.NONNULL;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Node;

/**
 * Base class for all nodes of the abstract syntax tree.
 * <h2>Construction</h2>
 * <p>The tree is built by instantiating the required nodes, then adding them to other nodes.
 * If it is the parser who is building the tree, it will use the largest constructor,
 * the one with "range" as the first parameter.
 * If you want to manually instantiate nodes, we suggest to...
 * <ul>
 * <li>use a convenience method, like "addStatement(...)", or if none are available...</li>
 * <li>use a convenient constructor, like ClassOrInterfaceType(String name), or if none are available...</li>
 * <li>use the default constructor.</li>
 * <li>Alternatively, use one of the JavaParser.parse(snippet) methods.</li>
 * </ul>
 * ... and use the various methods on the node to initialize it further, if needed.
 * <h2>Parent/child</h2>
 * <p>The parent node field is managed automatically and can be seen as read only.
 * Note that there is only one parent,
 * and trying to use the same node in two places will lead to unexpected behaviour.
 * It is advised to clone() a node before moving it around.
 * <h2>Comments</h2>
 * <p>Each Node can have one associated comment which describes it and
 * a number of "orphan comments" which it contains but are not specifically
 * associated to any child.
 * <h2>Positions</h2>
 * <p>When the parser creates nodes, it sets their source code position in the "range" field.
 * When you manually instantiate nodes, their range is not set.
 * The top left character is position 1, 1.
 * Note that since this is an <i>abstract</i> syntax tree,
 * it leaves out a lot of text from the original source file,
 * like where braces or comma's are exactly.
 * Therefore there is no position information on everything in the original source file.
 * <h2>Observers</h2>
 * <p>It is possible to add observers to the the tree.
 * Any change in the tree is sent as an event to any observers watching.
 * <h2>Visitors</h2>
 * <p>The most comfortable way of working with an abstract syntax tree is using visitors.
 * You can use one of the visitors in the visitor package, or extend one of them.
 * A visitor can be "run" by calling accept on a node:
 * <pre>node.accept(visitor, argument);</pre>
 * where argument is an object of your choice (often simply null.)
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Node implements Cloneable, HasParentNode<Node>, Visitable, NodeWithRange<Node>, NodeWithTokenRange<Node> {

    /**
     * Different registration mode for observers on nodes.
     */
    public enum ObserverRegistrationMode {

        /**
         * Notify exclusively for changes happening on this node alone.
         */
        JUST_THIS_NODE,
        /**
         * Notify for changes happening on this node and all its descendants existing at the moment in
         * which the observer was registered. Nodes attached later will not be observed.
         */
        THIS_NODE_AND_EXISTING_DESCENDANTS,
        /**
         * Notify for changes happening on this node and all its descendants. The descendants existing at the moment in
         * which the observer was registered will be observed immediately. As new nodes are attached later they are
         * automatically registered to be observed.
         */
        SELF_PROPAGATING
    }

    public enum Parsedness {

        PARSED, UNPARSABLE
    }

    /**
     * This can be used to sort nodes on position.
     */
    public static Comparator<NodeWithRange<?>> NODE_BY_BEGIN_POSITION = (a, b) -> {
        if (a.getRange().isPresent() && b.getRange().isPresent()) {
            return a.getRange().get().begin.compareTo(b.getRange().get().begin);
        }
        if (a.getRange().isPresent() || b.getRange().isPresent()) {
            if (a.getRange().isPresent()) {
                return 1;
            }
            return -1;
        }
        return 0;
    };

    private static PrettyPrinterConfiguration toStringPrettyPrinterConfiguration = new PrettyPrinterConfiguration();

    protected static final PrettyPrinterConfiguration prettyPrinterNoCommentsConfiguration = new PrettyPrinterConfiguration().setPrintComments(false);

    @InternalProperty
    private Range range;

    @InternalProperty
    private TokenRange tokenRange;

    @InternalProperty
    private Node parentNode;

    @InternalProperty
    private List<Node> childNodes = new LinkedList<>();

    @InternalProperty
    private List<Comment> orphanComments = new LinkedList<>();

    @InternalProperty
    private IdentityHashMap<DataKey<?>, Object> data = null;

    @OptionalProperty
    private Comment comment;

    @InternalProperty
    private List<AstObserver> observers = new ArrayList<>();

    @InternalProperty
    private Parsedness parsed = PARSED;

    protected Node(TokenRange tokenRange) {
        setTokenRange(tokenRange);
    }

    /**
     * Called in every constructor for node specific code.
     * It can't be written in the constructor itself because it will
     * be overwritten during code generation.
     */
    protected void customInitialization() {
    }

    /**
     * This is a comment associated with this node.
     *
     * @return comment property
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Comment> getComment() {
        return Optional.ofNullable(comment);
    }

    /**
     * @return the range of characters in the source code that this node covers.
     */
    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
    }

    /**
     * @return the range of tokens that this node covers.
     */
    public Optional<TokenRange> getTokenRange() {
        return Optional.ofNullable(tokenRange);
    }

    public Node setTokenRange(TokenRange tokenRange) {
        this.tokenRange = tokenRange;
        if (tokenRange == null || !(tokenRange.getBegin().getRange().isPresent() && tokenRange.getBegin().getRange().isPresent())) {
            range = null;
        } else {
            range = new Range(tokenRange.getBegin().getRange().get().begin, tokenRange.getEnd().getRange().get().end);
        }
        return this;
    }

    /**
     * @param range the range of characters in the source code that this node covers. null can be used to indicate that
     * no range information is known, or that it is not of interest.
     */
    public Node setRange(Range range) {
        if (this.range == range) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RANGE, this.range, range);
        this.range = range;
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setComment(final Comment comment) {
        if (this.comment == comment) {
            return this;
        }
        if (comment != null && (this instanceof Comment)) {
            throw new RuntimeException("A comment can not be commented");
        }
        notifyPropertyChange(ObservableProperty.COMMENT, this.comment, comment);
        if (this.comment != null) {
            this.comment.setCommentedNode(null);
        }
        this.comment = comment;
        if (comment != null) {
            this.comment.setCommentedNode(this);
        }
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setLineComment(String comment) {
        return setComment(new LineComment(comment));
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setBlockComment(String comment) {
        return setComment(new BlockComment(comment));
    }

    /**
     * @return pretty printed source code for this node and its children.
     * Formatting can be configured with Node.setToStringPrettyPrinterConfiguration.
     */
    @Override
    public final String toString() {
        return new PrettyPrinter(toStringPrettyPrinterConfiguration).print(this);
    }

    /**
     * @return pretty printed source code for this node and its children.
     * Formatting can be configured with parameter prettyPrinterConfiguration.
     */
    public final String toString(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        return new PrettyPrinter(prettyPrinterConfiguration).print(this);
    }

    @Override
    public final int hashCode() {
        return HashCodeVisitor.hashCode(this);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof Node)) {
            return false;
        }
        return EqualsVisitor.equals(this, (Node) obj);
    }

    @Override
    public Optional<Node> getParentNode() {
        return Optional.ofNullable(parentNode);
    }

    /**
     * Contains all nodes that have this node set as their parent.
     * You can add and remove nodes from this list by adding or removing nodes from the fields of this node.
     *
     * @return all nodes that have this node as their parent.
     */
    public List<Node> getChildNodes() {
        return unmodifiableList(childNodes);
    }

    public void addOrphanComment(Comment comment) {
        orphanComments.add(comment);
        comment.setParentNode(this);
    }

    public boolean removeOrphanComment(Comment comment) {
        boolean removed = orphanComments.remove(comment);
        if (removed) {
            notifyPropertyChange(ObservableProperty.COMMENT, comment, null);
            comment.setParentNode(null);
        }
        return removed;
    }

    /**
     * This is a list of Comment which are inside the node and are not associated
     * with any meaningful AST Node.
     * <p>
     * For example, comments at the end of methods (immediately before the parenthesis)
     * or at the end of CompilationUnit are orphan comments.
     * <p>
     * When more than one comment preceeds a statement, the one immediately preceding it
     * it is associated with the statements, while the others are orphans.
     * <p>
     * Changes to this list are not persisted.
     *
     * @return all comments that cannot be attributed to a concept
     */
    public List<Comment> getOrphanComments() {
        return new LinkedList<>(orphanComments);
    }

    /**
     * This is the list of Comment which are contained in the Node either because
     * they are properly associated to one of its children or because they are floating
     * around inside the Node
     *
     * @return all Comments within the node as a list
     */
    public List<Comment> getAllContainedComments() {
        List<Comment> comments = new LinkedList<>();
        comments.addAll(getOrphanComments());
        for (Node child : getChildNodes()) {
            child.getComment().ifPresent(comments::add);
            comments.addAll(child.getAllContainedComments());
        }
        return comments;
    }

    /**
     * Assign a new parent to this node, removing it
     * from the list of children of the previous parent, if any.
     *
     * @param newParentNode node to be set as parent
     */
    @Override
    public Node setParentNode(Node newParentNode) {
        if (newParentNode == parentNode) {
            return this;
        }
        observers.forEach(o -> o.parentChange(this, parentNode, newParentNode));
        // remove from old parent, if any
        if (parentNode != null) {
            final List<Node> parentChildNodes = parentNode.childNodes;
            for (int i = 0; i < parentChildNodes.size(); i++) {
                if (parentChildNodes.get(i) == this) {
                    parentChildNodes.remove(i);
                }
            }
        }
        parentNode = newParentNode;
        // add to new parent, if any
        if (parentNode != null) {
            parentNode.childNodes.add(this);
        }
        return this;
    }

    protected void setAsParentNodeOf(Node childNode) {
        if (childNode != null) {
            childNode.setParentNode(getParentNodeForChildren());
        }
    }

    public static final int ABSOLUTE_BEGIN_LINE = -1;

    public static final int ABSOLUTE_END_LINE = -2;

    public void tryAddImportToParentCompilationUnit(Class<?> clazz) {
        findAncestor(CompilationUnit.class).ifPresent(p -> p.addImport(clazz));
    }

    /**
     * Recursively finds all nodes of a certain type.
     *
     * @param clazz the type of node to find.
     * @deprecated use {@link Node#findAll(Class)} but be aware that findAll also considers the initial node.
     */
    @Deprecated
    public <N extends Node> List<N> getChildNodesByType(Class<N> clazz) {
        List<N> nodes = new ArrayList<>();
        for (Node child : getChildNodes()) {
            if (clazz.isInstance(child)) {
                nodes.add(clazz.cast(child));
            }
            nodes.addAll(child.getChildNodesByType(clazz));
        }
        return nodes;
    }

    /**
     * @deprecated use {@link Node#findAll(Class)} but be aware that findAll also considers the initial node.
     */
    @Deprecated
    public <N extends Node> List<N> getNodesByType(Class<N> clazz) {
        return getChildNodesByType(clazz);
    }

    /**
     * Gets data for this node using the given key.
     *
     * @param <M> The type of the data.
     * @param key The key for the data
     * @return The data.
     * @throws IllegalStateException if the key was not set in this node.
     * @see Node#containsData(DataKey)
     * @see DataKey
     */
    @SuppressWarnings("unchecked")
    public <M> M getData(final DataKey<M> key) {
        if (data == null) {
            throw new IllegalStateException("No data of this type found. Use containsData to check for this first.");
        }
        M value = (M) data.get(key);
        if (value == null) {
            throw new IllegalStateException("No data of this type found. Use containsData to check for this first.");
        }
        return value;
    }

    /**
     * This method was added to support the clone method.
     *
     * @return all known data keys.
     */
    public Set<DataKey<?>> getDataKeys() {
        if (data == null) {
            return emptySet();
        }
        return data.keySet();
    }

    /**
     * Sets data for this node using the given key.
     * For information on creating DataKey, see {@link DataKey}.
     *
     * @param <M> The type of data
     * @param key The singleton key for the data
     * @param object The data object
     * @see DataKey
     */
    public <M> void setData(DataKey<M> key, M object) {
        if (data == null) {
            data = new IdentityHashMap<>();
        }
        data.put(key, object);
    }

    /**
     * @return does this node have data for this key?
     * @see DataKey
     */
    public boolean containsData(DataKey<?> key) {
        if (data == null) {
            return false;
        }
        return data.containsKey(key);
    }

    /**
     * Remove data by key.
     *
     * @see DataKey
     */
    public void removeData(DataKey<ResolvedType> key) {
        if (data != null) {
            data.remove(key);
        }
    }

    /**
     * Try to remove this node from the parent
     *
     * @return true if removed, false if it is a required property of the parent, or if the parent isn't set.
     * @throws RuntimeException if it fails in an unexpected way
     */
    public boolean remove() {
        if (parentNode == null) {
            return false;
        }
        return parentNode.remove(this);
    }

    /**
     * Try to replace this node in the parent with the supplied node.
     *
     * @return true if removed, or if the parent isn't set.
     * @throws RuntimeException if it fails in an unexpected way
     */
    public boolean replace(Node node) {
        if (parentNode == null) {
            return false;
        }
        return parentNode.replace(this, node);
    }

    /**
     * Forcibly removes this node from the AST.
     * If it cannot be removed from the parent with remove(),
     * it will try to remove its parent instead,
     * until it finds a node that can be removed,
     * or no parent can be found.
     * <p>
     * Since everything at CompilationUnit level is removable,
     * this method will only (silently) fail when the node is in a detached AST fragment.
     */
    public void removeForced() {
        if (!remove()) {
            getParentNode().ifPresent(Node::remove);
        }
    }

    @Override
    public Node getParentNodeForChildren() {
        return this;
    }

    protected void setAsParentNodeOf(NodeList<? extends Node> list) {
        if (list != null) {
            list.setParentNode(getParentNodeForChildren());
        }
    }

    public <P> void notifyPropertyChange(ObservableProperty property, P oldValue, P newValue) {
        this.observers.forEach(o -> o.propertyChange(this, property, oldValue, newValue));
    }

    @Override
    public void unregister(AstObserver observer) {
        this.observers.remove(observer);
    }

    @Override
    public void register(AstObserver observer) {
        this.observers.add(observer);
    }

    /**
     * Register a new observer for the given node. Depending on the mode specified also descendants, existing
     * and new, could be observed. For more details see <i>ObserverRegistrationMode</i>.
     */
    public void register(AstObserver observer, ObserverRegistrationMode mode) {
        if (mode == null) {
            throw new IllegalArgumentException("Mode should be not null");
        }
        switch(mode) {
            case JUST_THIS_NODE:
                register(observer);
                break;
            case THIS_NODE_AND_EXISTING_DESCENDANTS:
                registerForSubtree(observer);
                break;
            case SELF_PROPAGATING:
                registerForSubtree(PropagatingAstObserver.transformInPropagatingObserver(observer));
                break;
            default:
                throw new UnsupportedOperationException("This mode is not supported: " + mode);
        }
    }

    /**
     * Register the observer for the current node and all the contained node and nodelists, recursively.
     */
    public void registerForSubtree(AstObserver observer) {
        register(observer);
        this.getChildNodes().forEach(c -> c.registerForSubtree(observer));
        for (PropertyMetaModel property : getMetaModel().getAllPropertyMetaModels()) {
            if (property.isNodeList()) {
                NodeList<?> nodeList = (NodeList<?>) property.getValue(this);
                if (nodeList != null)
                    nodeList.register(observer);
            }
        }
    }

    @Override
    public boolean isRegistered(AstObserver observer) {
        return this.observers.contains(observer);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (comment != null) {
            if (node == comment) {
                removeComment();
                return true;
            }
        }
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public Node removeComment() {
        return setComment((Comment) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public Node clone() {
        return (Node) accept(new CloneVisitor(), null);
    }

    /**
     * @return get JavaParser specific node introspection information.
     */
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public NodeMetaModel getMetaModel() {
        return JavaParserMetaModel.nodeMetaModel;
    }

    /**
     * @return whether this node was successfully parsed or not.
     * If it was not, only the range and tokenRange fields will be valid.
     */
    public Parsedness getParsed() {
        return parsed;
    }

    /**
     * Used by the parser to flag unparsable nodes.
     */
    public Node setParsed(Parsedness parsed) {
        this.parsed = parsed;
        return this;
    }

    public static PrettyPrinterConfiguration getToStringPrettyPrinterConfiguration() {
        return toStringPrettyPrinterConfiguration;
    }

    public static void setToStringPrettyPrinterConfiguration(PrettyPrinterConfiguration toStringPrettyPrinterConfiguration) {
        Node.toStringPrettyPrinterConfiguration = toStringPrettyPrinterConfiguration;
    }

    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (comment != null) {
            if (node == comment) {
                setComment((Comment) replacementNode);
                return true;
            }
        }
        return false;
    }

    /**
     * Finds the root node of this AST by finding the topmost parent.
     */
    public Node findRootNode() {
        Node n = this;
        while (n.getParentNode().isPresent()) {
            n = n.getParentNode().get();
        }
        return n;
    }

    /**
     * @return the containing CompilationUnit, or empty if this node is not inside a compilation unit.
     */
    public Optional<CompilationUnit> findCompilationUnit() {
        Node rootNode = findRootNode();
        if (rootNode instanceof CompilationUnit) {
            return Optional.of((CompilationUnit) rootNode);
        }
        return Optional.empty();
    }

    protected SymbolResolver getSymbolResolver() {
        return findCompilationUnit().map(cu -> {
            SymbolResolver symbolResolver = cu.getData(SYMBOL_RESOLVER_KEY);
            if (symbolResolver == null) {
                throw new IllegalStateException("Symbol resolution not configured: to configure consider setting a SymbolResolver in the ParserConfiguration");
            }
            return symbolResolver;
        }).orElseThrow(() -> new IllegalStateException("The node is not inserted in a CompilationUnit"));
    }

    // We need to expose it because we will need to use it to inject the SymbolSolver
    public static final DataKey<SymbolResolver> SYMBOL_RESOLVER_KEY = new DataKey<SymbolResolver>() {
    };

    public enum TreeTraversal {

        PREORDER, BREADTHFIRST, POSTORDER, PARENTS, DIRECT_CHILDREN
    }

    private Iterator<Node> treeIterator(TreeTraversal traversal) {
        switch(traversal) {
            case BREADTHFIRST:
                return new BreadthFirstIterator(this);
            case POSTORDER:
                return new PostOrderIterator(this);
            case PREORDER:
                return new PreOrderIterator(this);
            case DIRECT_CHILDREN:
                return new DirectChildrenIterator(this);
            case PARENTS:
                return new ParentsVisitor(this);
            default:
                throw new IllegalArgumentException("Unknown traversal choice.");
        }
    }

    private Iterable<Node> treeIterable(TreeTraversal traversal) {
        return () -> treeIterator(traversal);
    }

    /**
     * Make a stream of nodes using traversal algorithm "traversal".
     */
    public Stream<Node> stream(TreeTraversal traversal) {
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(treeIterator(traversal), NONNULL | DISTINCT), false);
    }

    /**
     * Make a stream of nodes using pre-order traversal.
     */
    public Stream<Node> stream() {
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(treeIterator(PREORDER), NONNULL | DISTINCT), false);
    }

    /**
     * Walks the AST, calling the consumer for every node, with traversal algorithm "traversal".
     * <br/>This is the most general walk method. All other walk and findAll methods are based on this.
     */
    public void walk(TreeTraversal traversal, Consumer<Node> consumer) {
        // Could be implemented as a call to the above walk method, but this is a little more efficient.
        for (Node node : treeIterable(traversal)) {
            consumer.accept(node);
        }
    }

    /**
     * Walks the AST, calling the consumer for every node with pre-order traversal.
     */
    public void walk(Consumer<Node> consumer) {
        walk(PREORDER, consumer);
    }

    /**
     * Walks the AST with pre-order traversal, calling the consumer for every node of type "nodeType".
     */
    public <T extends Node> void walk(Class<T> nodeType, Consumer<T> consumer) {
        walk(TreeTraversal.PREORDER, node -> {
            if (nodeType.isAssignableFrom(node.getClass())) {
                consumer.accept(nodeType.cast(node));
            }
        });
    }

    /**
     * Walks the AST with pre-order traversal, returning all nodes of type "nodeType".
     */
    public <T extends Node> List<T> findAll(Class<T> nodeType) {
        final List<T> found = new ArrayList<>();
        walk(nodeType, found::add);
        return found;
    }

    /**
     * Walks the AST with pre-order traversal, returning all nodes of type "nodeType" that match the predicate.
     */
    public <T extends Node> List<T> findAll(Class<T> nodeType, Predicate<T> predicate) {
        final List<T> found = new ArrayList<>();
        walk(nodeType, n -> {
            if (predicate.test(n))
                found.add(n);
        });
        return found;
    }

    /**
     * Walks the AST, applying the function for every node, with traversal algorithm "traversal". If the function
     * returns something else than null, the traversal is stopped and the function result is returned. <br/>This is the
     * most general findFirst method. All other findFirst methods are based on this.
     */
    public <T> Optional<T> findFirst(TreeTraversal traversal, Function<Node, Optional<T>> consumer) {
        for (Node node : treeIterable(traversal)) {
            final Optional<T> result = consumer.apply(node);
            if (result.isPresent()) {
                return result;
            }
        }
        return Optional.empty();
    }

    /**
     * Walks the AST with pre-order traversal, returning the first node of type "nodeType" or empty() if none is found.
     */
    public <N extends Node> Optional<N> findFirst(Class<N> nodeType) {
        return findFirst(TreeTraversal.PREORDER, node -> {
            if (nodeType.isAssignableFrom(node.getClass())) {
                return Optional.of(nodeType.cast(node));
            }
            return Optional.empty();
        });
    }

    /**
     * Walks the AST with pre-order traversal, returning the first node of type "nodeType" that matches "predicate" or empty() if none is
     * found.
     */
    public <N extends Node> Optional<N> findFirst(Class<N> nodeType, Predicate<N> predicate) {
        return findFirst(TreeTraversal.PREORDER, node -> {
            if (nodeType.isAssignableFrom(node.getClass())) {
                final N castNode = nodeType.cast(node);
                if (predicate.test(castNode)) {
                    return Optional.of(castNode);
                }
            }
            return Optional.empty();
        });
    }

    /**
     * Performs a breadth-first node traversal starting with a given node.
     *
     * @see <a href="https://en.wikipedia.org/wiki/Breadth-first_search">Breadth-first traversal</a>
     */
    public static class BreadthFirstIterator implements Iterator<Node> {

        private final Queue<Node> queue = new LinkedList<>();

        public BreadthFirstIterator(Node node) {
            queue.add(node);
        }

        @Override
        public boolean hasNext() {
            return !queue.isEmpty();
        }

        @Override
        public Node next() {
            Node next = queue.remove();
            queue.addAll(next.getChildNodes());
            return next;
        }
    }

    /**
     * Performs a simple traversal over all nodes that have the passed node as their parent.
     */
    public static class DirectChildrenIterator implements Iterator<Node> {

        private final Iterator<Node> childrenIterator;

        public DirectChildrenIterator(Node node) {
            childrenIterator = new ArrayList<>(node.getChildNodes()).iterator();
        }

        @Override
        public boolean hasNext() {
            return childrenIterator.hasNext();
        }

        @Override
        public Node next() {
            return childrenIterator.next();
        }
    }

    /**
     * Iterates over the parent of the node, then the parent's parent, then the parent's parent's parent, until running
     * out of parents.
     */
    public static class ParentsVisitor implements Iterator<Node> {

        private Node node;

        public ParentsVisitor(Node node) {
            this.node = node;
        }

        @Override
        public boolean hasNext() {
            return node.getParentNode().isPresent();
        }

        @Override
        public Node next() {
            node = node.getParentNode().orElse(null);
            return node;
        }
    }

    /**
     * Performs a pre-order (or depth-first) node traversal starting with a given node.
     *
     * @see <a href="https://en.wikipedia.org/wiki/Pre-order">Pre-order traversal</a>
     */
    public static class PreOrderIterator implements Iterator<Node> {

        private final Stack<Node> stack = new Stack<>();

        public PreOrderIterator(Node node) {
            stack.add(node);
        }

        @Override
        public boolean hasNext() {
            return !stack.isEmpty();
        }

        @Override
        public Node next() {
            Node next = stack.pop();
            List<Node> children = next.getChildNodes();
            for (int i = children.size() - 1; i >= 0; i--) {
                stack.add(children.get(i));
            }
            return next;
        }
    }

    /**
     * Performs a post-order (or leaves-first) node traversal starting with a given node.
     *
     * @see <a href="https://en.wikipedia.org/wiki/Post-order">Post-order traversal</a>
     */
    public static class PostOrderIterator implements Iterator<Node> {

        private final Stack<List<Node>> nodesStack = new Stack<>();

        private final Stack<Integer> cursorStack = new Stack<>();

        private final Node root;

        private boolean hasNext = true;

        public PostOrderIterator(Node root) {
            this.root = root;
            fillStackToLeaf(root);
        }

        private void fillStackToLeaf(Node node) {
            while (true) {
                List<Node> childNodes = new ArrayList<>(node.getChildNodes());
                if (childNodes.isEmpty()) {
                    break;
                }
                nodesStack.push(childNodes);
                cursorStack.push(0);
                node = childNodes.get(0);
            }
        }

        @Override
        public boolean hasNext() {
            return hasNext;
        }

        @Override
        public Node next() {
            final List<Node> nodes = nodesStack.peek();
            final int cursor = cursorStack.peek();
            final boolean levelHasNext = cursor < nodes.size();
            if (levelHasNext) {
                Node node = nodes.get(cursor);
                fillStackToLeaf(node);
                return nextFromLevel();
            } else {
                nodesStack.pop();
                cursorStack.pop();
                hasNext = !nodesStack.empty();
                if (hasNext) {
                    return nextFromLevel();
                }
                return root;
            }
        }

        private Node nextFromLevel() {
            final List<Node> nodes = nodesStack.peek();
            final int cursor = cursorStack.pop();
            cursorStack.push(cursor + 1);
            return nodes.get(cursor);
        }
    }
}
