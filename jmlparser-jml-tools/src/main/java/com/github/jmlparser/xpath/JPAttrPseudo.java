package com.github.jmlparser.xpath;

import org.jetbrains.annotations.NotNull;
import org.w3c.dom.*;

import java.util.function.Supplier;

/**
 * @author Alexander Weigl
 * @version 1 (01.12.22)
 */
public class JPAttrPseudo implements org.w3c.dom.Attr {
    final String name;
    final Supplier<String> supplier;
    final Element owner;

    public JPAttrPseudo(String name, Supplier<String> supplier, Element owner) {
        this.name = name;
        this.supplier = supplier;
        this.owner = owner;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean getSpecified() {
        return true;
    }

    @Override
    public String getValue() {
        return supplier.get();
    }

    @Override
    public void setValue(String value) throws DOMException {
        throw new IllegalStateException();
    }

    @Override
    public Element getOwnerElement() {
        return owner;
    }

    @Override
    public TypeInfo getSchemaTypeInfo() {
        return null;
    }

    @Override
    public boolean isId() {
        return false;
    }

    @NotNull
    @Override
    public String getNodeName() {
        return getName();
    }

    @Override
    public String getNodeValue() throws DOMException {
        return getValue();
    }

    @Override
    public void setNodeValue(String nodeValue) throws DOMException {
        throw new RuntimeException();
    }

    @Override
    public short getNodeType() {
        return ATTRIBUTE_NODE;
    }

    @Override
    public Node getParentNode() {
        return getOwnerElement();
    }

    @NotNull
    @Override
    public NodeList getChildNodes() {
        return DocumentFactories.wrap();
    }

    @Override
    public Node getFirstChild() {
        return null;
    }

    @Override
    public Node getLastChild() {
        return null;
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
        return null;
    }

    @Override
    public Document getOwnerDocument() {
        return getParentNode().getOwnerDocument();
    }

    @Override
    public Node insertBefore(Node newChild, Node refChild) throws DOMException {
        return null;
    }

    @Override
    public Node replaceChild(Node newChild, Node oldChild) throws DOMException {
        return null;
    }

    @Override
    public Node removeChild(Node oldChild) throws DOMException {
        return null;
    }

    @Override
    public Node appendChild(Node newChild) throws DOMException {
        return null;
    }

    @Override
    public boolean hasChildNodes() {
        return false;
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
        return getValue();
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
