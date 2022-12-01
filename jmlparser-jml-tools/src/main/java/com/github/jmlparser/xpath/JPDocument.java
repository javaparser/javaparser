package com.github.jmlparser.xpath;

import com.github.javaparser.ast.CompilationUnit;
import org.jetbrains.annotations.NotNull;
import org.w3c.dom.*;

import java.util.List;

import static org.w3c.dom.DOMException.NOT_SUPPORTED_ERR;

public class JPDocument implements Document {
    final JPRootElement root;

    public JPDocument(CompilationUnit node) {
        root = new JPRootElement(List.of(node), this);
    }

    @Override
    public DocumentType getDoctype() {
        return null;
    }

    @Override
    public DOMImplementation getImplementation() {
        return null;
    }

    @Override
    public Element getDocumentElement() {
        return root;
    }

    @Override
    public Element createElement(String tagName) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public DocumentFragment createDocumentFragment() {
        return null;
    }

    @Override
    public Text createTextNode(String data) {
        return null;
    }

    @Override
    public Comment createComment(String data) {
        return null;
    }

    @Override
    public CDATASection createCDATASection(String data) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public ProcessingInstruction createProcessingInstruction(String target, String data) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Attr createAttribute(String name) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public EntityReference createEntityReference(String name) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public NodeList getElementsByTagName(String tagname) {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Node importNode(Node importedNode, boolean deep) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Element createElementNS(String namespaceURI, String qualifiedName) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");

    }

    @Override
    public Attr createAttributeNS(String namespaceURI, String qualifiedName) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public NodeList getElementsByTagNameNS(String namespaceURI, String localName) {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public Element getElementById(String elementId) {
        return null;
    }

    @Override
    public String getInputEncoding() {
        return "utf-8";
    }

    @Override
    public String getXmlEncoding() {
        return "utf-8";
    }

    @Override
    public boolean getXmlStandalone() {
        return true;
    }

    @Override
    public void setXmlStandalone(boolean xmlStandalone) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @Override
    public String getXmlVersion() {
        return "1.0";
    }

    @Override
    public void setXmlVersion(String xmlVersion) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");

    }

    @Override
    public boolean getStrictErrorChecking() {
        return false;
    }

    @Override
    public void setStrictErrorChecking(boolean strictErrorChecking) {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");

    }

    @Override
    public String getDocumentURI() {
        return null;
    }

    @Override
    public void setDocumentURI(String documentURI) {

    }

    @Override
    public Node adoptNode(Node source) throws DOMException {
        return null;
    }

    @Override
    public DOMConfiguration getDomConfig() {
        return null;
    }

    @Override
    public void normalizeDocument() {

    }

    @Override
    public Node renameNode(Node n, String namespaceURI, String qualifiedName) throws DOMException {
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
    }

    @NotNull
    @Override
    public String getNodeName() {
        return "#document";
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
        return DOCUMENT_TYPE_NODE;
    }

    @Override
    public Node getParentNode() {
        return null;
    }

    @NotNull
    @Override
    public NodeList getChildNodes() {
        return DocumentFactories.wrap(root);
    }

    @Override
    public Node getFirstChild() {
        return root;
    }

    @Override
    public Node getLastChild() {
        return root;
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
        return this;
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
        return root != null;
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
        throw new DOMException(NOT_SUPPORTED_ERR, "Not Supported");
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
