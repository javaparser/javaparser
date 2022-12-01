package com.github.jmlparser.xpath;


import com.github.javaparser.ast.CompilationUnit;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.w3c.dom.*;

import java.util.List;
import java.util.stream.Collectors;

import static org.w3c.dom.DOMException.NOT_SUPPORTED_ERR;

public class JPRootElement implements Element {
    private final List<CompilationUnit> nodes;
    @Nullable
    private List<Element> elements;
    private final JPDocument document;

    public JPRootElement(List<CompilationUnit> compilationUnits, JPDocument document) {
        this.nodes = compilationUnits;
        this.document = document;
    }

    @NotNull
    private List<Element> lazyElements() {
        if (elements == null) {
            elements = nodes.stream()
                    .map(it -> DocumentFactories.getElement(it, this))
                    .collect(Collectors.toList());
        }
        return elements;
    }

    @Override
    public String getTagName() {
        return "project";
    }

    @NotNull
    @Override
    public String getAttribute(String name) {
        return "";
    }

    @Override
    public void setAttribute(String name, String value) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public void removeAttribute(String name) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Attr getAttributeNode(String name) {
        return null;
    }

    @Override
    public Attr setAttributeNode(Attr newAttr) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Attr removeAttributeNode(Attr oldAttr) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @NotNull
    @Override
    public NodeList getElementsByTagName(String name) {
        throw new IllegalStateException();
    }

    @NotNull
    @Override
    public String getAttributeNS(String namespaceURI, String localName) throws DOMException {
        return "";
    }

    @Override
    public void setAttributeNS(String namespaceURI, String qualifiedName, String value) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public void removeAttributeNS(String namespaceURI, String localName) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Attr getAttributeNodeNS(String namespaceURI, String localName) throws DOMException {
        return null;
    }

    @Override
    public Attr setAttributeNodeNS(Attr newAttr) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @NotNull
    @Override
    public NodeList getElementsByTagNameNS(String namespaceURI, String localName) throws DOMException {
        throw new IllegalStateException();
    }

    @Override
    public boolean hasAttribute(String name) {
        return false;
    }

    @Override
    public boolean hasAttributeNS(String namespaceURI, String localName) throws DOMException {
        return false;
    }

    @Override
    public TypeInfo getSchemaTypeInfo() {
        return null;
    }

    @Override
    public void setIdAttribute(String name, boolean isId) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public void setIdAttributeNS(String namespaceURI, String localName, boolean isId) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public void setIdAttributeNode(Attr idAttr, boolean isId) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @NotNull
    @Override
    public String getNodeName() {
        return getTagName();
    }

    @Override
    public String getNodeValue() throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public void setNodeValue(String nodeValue) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public short getNodeType() {
        return ELEMENT_NODE;
    }

    @Override
    public Node getParentNode() {
        return document;
    }

    @NotNull
    @Override
    public NodeList getChildNodes() {
        return DocumentFactories.wrap(lazyElements());
    }

    @Override
    public Node getFirstChild() {
        return lazyElements().get(0);
    }

    @Override
    public Node getLastChild() {
        return lazyElements().get(lazyElements().size() - 1);
    }

    @Override
    public Node getPreviousSibling() {
        return null;
    }

    @Override
    public Node getNextSibling() {
        return null;
    }

    @Override
    public NamedNodeMap getAttributes() {
        return DocumentFactories.emptyNodeMap();
    }

    @Override
    public Document getOwnerDocument() {
        return document;
    }

    @Override
    public Node insertBefore(Node newChild, Node refChild) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Node replaceChild(Node newChild, Node oldChild) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Node removeChild(Node oldChild) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Node appendChild(Node newChild) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public boolean hasChildNodes() {
        return !lazyElements().isEmpty();
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
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
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
        return "";
    }

    @Override
    public void setTextContent(String textContent) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public boolean isSameNode(Node other) {
        return other instanceof JPRootElement o &&
                this.document == o.document;
    }

    @Override
    public String lookupPrefix(String namespaceURI) {
        return "";
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