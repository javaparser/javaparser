package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;

/**
 * @author Federico Tomassetti
 */
public interface ObjectProvider {
    ReferenceType object();
    ReferenceType byName(String qname);
}
