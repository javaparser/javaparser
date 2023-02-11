package com.github.jmlparser.xpath;

import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.w3c.dom.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
class JPElement implements Element {
    public com.github.javaparser.ast.Node getAstNode() {
        return astNode;
    }

    final com.github.javaparser.ast.Node astNode;
    final NodeMetaModel meta;

    private final Element parent;
    int posInParent;

    @Nullable
    private List<JPElement> children = null;

    private List<Attr> attributes = null;


    JPElement(com.github.javaparser.ast.Node astNode, Element parent) {
        this.parent = parent;
        this.astNode = astNode;
        meta = astNode.getMetaModel();
    }

    @Nullable
    List<JPElement> lazyChildren() {
        if (children == null) {
            children = meta.getAllPropertyMetaModels()
                    .stream()
                    .filter(DocumentFactories::isNodeProperty)
                    .map(it -> it.getValue(this.astNode))
                    .flatMap(it -> {
                        if (it instanceof com.github.javaparser.ast.NodeList<?> seq) {
                            return seq.stream().map(
                                    n -> DocumentFactories.getElement(n, this));
                        } else if (it instanceof com.github.javaparser.ast.Node n) {
                            return Stream.of(DocumentFactories.getElement(n, this));
                        }
                        return null;
                    })
                    .map(JPElement.class::cast)
                    .toList();
            for (int i = 0; i < children.size(); i++) {
                children.get(i).posInParent = i;
            }
        }
        return children;
    }

    @NotNull
    List<Attr> lazyAttributes() {
        if (attributes == null) {
            var attr = meta.getAllPropertyMetaModels()
                    .stream()
                    .filter(it -> !DocumentFactories.isNodeProperty(it))
                    .map(it -> DocumentFactories.getAttribute(this, it))
                    .map(Attr.class::cast)
                    .toList();
            attributes = new ArrayList<>(attr);
            for (PseudoAttributeProvider provider : DocumentFactories.getAttributeProviders()) {
                var seq = provider.attributeForNode(astNode, this);
                if (seq != null) {
                    attributes.addAll(seq);
                }
            }
        }
        return attributes;
    }

    @Override
    public String getTagName() {
        return meta.getTypeName();
    }

    @NotNull
    @Override
    public String getAttribute(String name) {
        var prop = getProperty(name);
        return prop.getValue(astNode).toString();
    }

    PropertyMetaModel getProperty(String name) {
        return meta.getAllPropertyMetaModels().stream()
                .filter(it -> it.getName().equals(name))
                .findFirst().orElse(null);
    }

    @Override
    public void setAttribute(String name, String value) throws DOMException {
        throw new IllegalStateException();
    }

    @Override
    public void removeAttribute(String name) throws DOMException {
        throw new IllegalStateException();
    }

    @Override
    public Attr getAttributeNode(String name) {
        return lazyAttributes().stream()
                .filter(it -> it.getName().equals(name))
                .findFirst().orElse(null);
    }

    @Override
    public Attr setAttributeNode(Attr newAttr) throws DOMException {
        return null;
    }

    @Override
    public Attr removeAttributeNode(Attr oldAttr) throws DOMException {
        return null;
    }

    @NotNull
    @Override
    public NodeList getElementsByTagName(String name) {
        throw new IllegalStateException();
    }

    @NotNull
    @Override
    public String getAttributeNS(String namespaceURI, String localName) throws DOMException {
        throw new IllegalStateException();

    }

    @Override
    public void setAttributeNS(String namespaceURI, String qualifiedName, String value) throws DOMException {
        throw new IllegalStateException();

    }

    @Override
    public void removeAttributeNS(String namespaceURI, String localName) throws DOMException {
        throw new IllegalStateException();

    }

    @Override
    public Attr getAttributeNodeNS(String namespaceURI, String localName) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public Attr setAttributeNodeNS(Attr newAttr) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @NotNull
    @Override
    public NodeList getElementsByTagNameNS(String namespaceURI, String localName) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public boolean hasAttribute(String name) {
        return !meta.getAllPropertyMetaModels().isEmpty();
    }

    @Override
    public boolean hasAttributeNS(String namespaceURI, String localName) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public TypeInfo getSchemaTypeInfo() {
        return null;
    }

    @Override
    public void setIdAttribute(String name, boolean isId) throws DOMException {

    }

    @Override
    public void setIdAttributeNS(String namespaceURI, String localName, boolean isId) throws DOMException {

    }

    @Override
    public void setIdAttributeNode(Attr idAttr, boolean isId) throws DOMException {

    }

    @NotNull
    @Override
    public String getNodeName() {
        return getTagName();
    }

    @Override
    public String getNodeValue() throws DOMException {
        return "";
    }

    @Override
    public void setNodeValue(String nodeValue) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public short getNodeType() {
        return ELEMENT_NODE;
    }

    @Override
    public Node getParentNode() {
        return parent;
    }

    @NotNull
    @Override
    public NodeList getChildNodes() {
        return DocumentFactories.wrap(lazyChildren());
    }

    @Override
    public Node getFirstChild() {
        if (hasChildNodes())
            return lazyChildren().get(0);
        else
            return null;
    }

    @Override
    public Node getLastChild() {
        if (hasChildNodes())
            return lazyChildren().get(lazyChildren().size() - 1);
        else
            return null;
    }

    @Override
    public Node getPreviousSibling() {
        if (parent != null && posInParent != 0) {
            return parent.getChildNodes().item(posInParent - 1);
        }
        return null;
    }

    @Override
    public Node getNextSibling() {
        if (parent != null && posInParent + 1 < parent.getChildNodes().getLength()) {
            return parent.getChildNodes().item(posInParent + 1);
        }
        return null;
    }

    @Override
    public NamedNodeMap getAttributes() {
        return DocumentFactories.nodeMap(this);
    }

    @Override
    public Document getOwnerDocument() {
        return parent != null ? parent.getOwnerDocument() : null;
    }

    @Override
    public Node insertBefore(Node newChild, Node refChild) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public Node replaceChild(Node newChild, Node oldChild) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public Node removeChild(Node oldChild) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public Node appendChild(Node newChild) throws DOMException {
        throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
    }

    @Override
    public boolean hasChildNodes() {
        return lazyChildren().size() != 0;
    }

    @Override
    public Node cloneNode(boolean deep) {
        return null;
    }

    @Override
    public void normalize() {

    }

    @Override
    public boolean isSupported(String feature, String version) {
        return false;
    }

    @Override
    public String getNamespaceURI() {
        return null;
    }

    @Override
    public String getPrefix() {
        return null;
    }

    @Override
    public void setPrefix(String prefix) throws DOMException {

    }

    @Override
    public String getLocalName() {
        return null;
    }

    @Override
    public boolean hasAttributes() {
        return false;
    }

    @Override
    public String getBaseURI() {
        return null;
    }

    @Override
    public short compareDocumentPosition(Node other) throws DOMException {
        return 0;
    }

    @Override
    public String getTextContent() throws DOMException {
        return null;
    }

    @Override
    public void setTextContent(String textContent) throws DOMException {

    }

    @Override
    public boolean isSameNode(Node other) {
        return false;
    }

    @Override
    public String lookupPrefix(String namespaceURI) {
        return null;
    }

    @Override
    public boolean isDefaultNamespace(String namespaceURI) {
        return false;
    }

    @Override
    public String lookupNamespaceURI(String prefix) {
        return null;
    }

    @Override
    public boolean isEqualNode(Node arg) {
        return false;
    }

    @Override
    public Object getFeature(String feature, String version) {
        return null;
    }

    @Override
    public Object setUserData(String key, Object data, UserDataHandler handler) {
        return null;
    }

    @Override
    public Object getUserData(String key) {
        return null;
    }
}
