package com.github.jmlparser.xpath;


import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.metamodel.PropertyMetaModel;
import org.jaxen.*;
import org.jaxen.dom.DOMXPath;
import org.jaxen.saxpath.SAXPathException;
import org.jaxen.util.SingleObjectIterator;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
public class AstNavigator extends DefaultNavigator {
    static class AttrNodeWrap {
        final Node n;
        final PropertyMetaModel pmm;

        AttrNodeWrap(Node n, PropertyMetaModel pmm) {
            this.n = n;
            this.pmm = pmm;
        }
    }

    private final transient JavaParser jp;

    public AstNavigator(JavaParser jp) {
        this.jp = jp;
    }

    @Override
    public Iterator<Object> getChildAxisIterator(Object contextNode) {
        var node = (Node) contextNode;
        return node.getChildNodes().stream().map(Object.class::cast).iterator();
    }

    @Override
    public Iterator<Object> getDescendantAxisIterator(Object contextNode) {
        return new Iterator<>() {
            final Queue<Node> deliver = new LinkedList<>();
            final Queue<Node> explore = new LinkedList<>();

            {
                explore.add((Node) contextNode);
            }

            @Override
            public boolean hasNext() {
                if (deliver.isEmpty()) explore();
                return !deliver.isEmpty();
            }

            @Override
            public Object next() {
                if (deliver.isEmpty()) explore();
                return deliver.poll();
            }

            private void explore() {
                if (!explore.isEmpty()) {
                    Node n = explore.poll();
                    deliver.addAll(n.getChildNodes());
                    explore.addAll(n.getChildNodes());
                }
            }
        };
    }

    @Override
    public Iterator<Object> getParentAxisIterator(Object contextNode) {
        Node n = (Node) contextNode;
        if (n.hasParentNode())
            return new SingleObjectIterator(n.getParentNode().get());
        else
            return JaxenConstants.EMPTY_ITERATOR;
    }

    @Override
    public Iterator<Object> getAncestorAxisIterator(Object contextNode) {
        return new Iterator<>() {
            Node cur = (Node) contextNode;

            @Override
            public boolean hasNext() {
                return cur.hasParentNode();
            }

            @Override
            public Object next() {
                if (cur.getParentNode().isPresent()) {
                    cur = cur.getParentNode().get();
                } else {
                    throw new NoSuchElementException();
                }
                return cur;
            }
        };
    }

    @Override
    public Iterator<Object> getAttributeAxisIterator(Object contextNode) {
        var n = (Node) contextNode;
        return n.getMetaModel().getAllPropertyMetaModels().stream()
                .map(pmm -> (Object) new AttrNodeWrap(n, pmm)).iterator();
    }


    @Override
    public Object getDocument(String uri) throws FunctionCallException {
        try {
            var r = jp.parse(Paths.get(uri));
            if (r.getResult().isPresent()) return r.getResult().get();
            throw new FunctionCallException("Could not load java file: " + uri + " due to problems: " + r.getProblems());
        } catch (IOException e) {
            throw new FunctionCallException("Could not load java file: " + uri, e);
        }
    }

    @Override
    public Object getDocumentNode(Object contextNode) {
        return null;
    }

    @Override
    public Object getParentNode(Object contextNode) {
        if (contextNode instanceof Node)
            return ((Node) contextNode).getParentNode().orElse(null);
        if (contextNode instanceof AttrNodeWrap)
            return ((AttrNodeWrap) contextNode).n;
        return null;
    }

    @Override
    public String getElementNamespaceUri(Object element) {
        return null;
    }

    @Override
    public String getElementName(Object element) {
        return ((Node) element).getMetaModel().getTypeName();
    }

    @Override
    public String getElementQName(Object element) {
        return null;
    }

    @Override
    public String getAttributeNamespaceUri(Object attr) {
        return "";
    }

    @Override
    public String getAttributeName(Object attr) {
        return ((AttrNodeWrap) attr).pmm.getName();
    }

    @Override
    public String getAttributeQName(Object attr) {
        return ((AttrNodeWrap) attr).pmm.getName();
    }

    @Override
    public String getProcessingInstructionTarget(Object pi) {
        return null;
    }

    @Override
    public String getProcessingInstructionData(Object pi) {
        return null;
    }

    @Override
    public boolean isDocument(Object object) {
        return object instanceof CompilationUnit;
    }

    @Override
    public boolean isElement(Object object) {
        return object instanceof Node;
    }

    @Override
    public boolean isAttribute(Object object) {
        return object instanceof AttrNodeWrap;
    }

    @Override
    public boolean isNamespace(Object object) {
        return false;
    }

    @Override
    public boolean isComment(Object object) {
        return object instanceof Comment;
    }

    @Override
    public boolean isText(Object object) {
        return object instanceof String;
    }

    @Override
    public boolean isProcessingInstruction(Object object) {
        return false;
    }

    @Override
    public String getCommentStringValue(Object comment) {
        return ((Comment) comment).getContent();
    }

    @Override
    public String getElementStringValue(Object element) {
        return element.toString();
    }

    @Override
    public String getAttributeStringValue(Object attr) {
        var a = ((AttrNodeWrap) attr);
        return a.pmm.getValue(a.n).toString();
    }

    @Override
    public String getNamespaceStringValue(Object ns) {
        return null;
    }

    @Override
    public String getTextStringValue(Object text) {
        return null;
    }

    @Override
    public String getNamespacePrefix(Object ns) {
        return null;
    }

    @Override
    public String translateNamespacePrefixToUri(String prefix, Object element) {
        return null;
    }

    @Override
    public XPath parseXPath(String xpath) throws SAXPathException {
        return new DOMXPath(xpath);
    }
}
