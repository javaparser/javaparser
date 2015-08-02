package me.tomassetti.symbolsolver.model;

import com.sun.xml.internal.messaging.saaj.packaging.mime.internet.HeaderTokenizer;

/**
 * Created by federico on 28/07/15.
 */
public interface MethodDeclaration extends SymbolDeclaration {
    TypeDeclaration getType();

    TypeDeclaration getReturnType();

    int getNoParams();

    ParameterDeclaration getParam(int i);
}
