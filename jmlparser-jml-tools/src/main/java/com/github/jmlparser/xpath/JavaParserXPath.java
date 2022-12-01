package com.github.jmlparser.xpath;

import com.github.javaparser.JavaParser;
import org.jaxen.BaseXPath;
import org.jaxen.JaxenException;

/**
 * @author Alexander Weigl
 * @version 1 (30.11.22)
 */
public class JavaParserXPath extends BaseXPath {
    public JavaParserXPath(String xpath, JavaParser jp) throws JaxenException {
        super(xpath, new AstNavigator(jp));
    }
}
