package com.github.jmlparser.xpath;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.metamodel.PropertyMetaModel;
import org.w3c.dom.*;

import java.util.List;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
public class DocumentFactories {
    private static List<PseudoAttributeProvider> providerList = null;

    public static List<PseudoAttributeProvider> getAttributeProviders() {
        if (providerList == null) {
            var sl = ServiceLoader.load(PseudoAttributeProvider.class);
            return providerList = sl.stream().map(ServiceLoader.Provider::get).toList();
        }
        return providerList;
    }

    public static boolean isNodeProperty(PropertyMetaModel mm) {
        return mm.isNode() || mm.isNodeList();
    }

    public static Document getDocument(CompilationUnit node) {
        return new JPDocument(node);
    }

    public static JPElement getElement(com.github.javaparser.ast.Node it, Element parent) {
        return new JPElement(it, parent);
    }


    public static <T extends Node> NodeList wrap(List<T> list) {
        return new NodeList() {
            @Override
            public Node item(int index) {
                return list.get(index);
            }

            @Override
            public int getLength() {
                return list.size();
            }
        };
    }

    public static NodeList wrap(Element... seq) {
        return wrap(List.of(seq));
    }

    public static NamedNodeMap emptyNodeMap() {
        return new NamedNodeMap() {
            @Override
            public Node getNamedItem(String name) {
                return null;
            }

            @Override
            public Node setNamedItem(Node arg) throws DOMException {
                return null;
            }

            @Override
            public Node removeNamedItem(String name) throws DOMException {
                return null;
            }

            @Override
            public Node item(int index) {
                return null;
            }

            @Override
            public int getLength() {
                return 0;
            }

            @Override
            public Node getNamedItemNS(String namespaceURI, String localName) throws DOMException {
                return null;
            }

            @Override
            public Node setNamedItemNS(Node arg) throws DOMException {
                return null;
            }

            @Override
            public Node removeNamedItemNS(String namespaceURI, String localName) throws DOMException {
                return null;
            }
        };
    }

    public static Attr getAttribute(JPElement jpElement, PropertyMetaModel it) {
        return new JPAttr(jpElement, it);
    }

    public static NamedNodeMap nodeMap(JPElement jpElement) {
        return new NamedNodeMap() {
            @Override
            public Node getNamedItem(String name) {
                return jpElement.lazyAttributes().stream()
                        .filter(it -> it.getName().equals(name))
                        .findFirst().orElse(null);
            }

            @Override
            public Node setNamedItem(Node arg) throws DOMException {
                throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
            }

            @Override
            public Node removeNamedItem(String name) throws DOMException {
                throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
            }

            @Override
            public Node item(int index) {
                return jpElement.lazyAttributes().get(index);
            }

            @Override
            public int getLength() {
                return jpElement.lazyAttributes().size();
            }

            @Override
            public Node getNamedItemNS(String namespaceURI, String localName) throws DOMException {
                throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
            }

            @Override
            public Node setNamedItemNS(Node arg) throws DOMException {
                throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
            }

            @Override
            public Node removeNamedItemNS(String namespaceURI, String localName) throws DOMException {
                throw new DOMException(DOMException.NOT_SUPPORTED_ERR, "");
            }
        };
    }
}
