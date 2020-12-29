/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static java.util.Collections.synchronizedMap;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Optional;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.type.UnknownType;

/**
 * We want to recognize and ignore "phantom" nodes, like the fake type of variable in FieldDeclaration
 */
public class PhantomNodeLogic {

    private static final int LEVELS_TO_EXPLORE = 3;
    
    private static final Integer DEFAULT_CACHE_REGION = Integer.valueOf(-1);

    /*
     * This global cache is deprecated to offer the possibility to partially clean the cache  
     * @deprecated @see isPhantomNodeCachePerCU
     */
    @Deprecated
    private static final Map<Node, Boolean> isPhantomNodeCache = synchronizedMap(new IdentityHashMap<>());
    
    /*
     * This is a cache per CompilationUnit to offer the possibility to partially clean the cache.
     */
    private static final Map<Integer, Map<Node, Boolean>> isPhantomNodeCachePerCU = new HashMap<>();
    
    private static final Map<Integer, CacheStats> stats = new HashMap<>(); 

    private static final AstObserver cacheCleaner = new AstObserverAdapter() {
        @Override
        public void parentChange(Node observedNode, Node previousParent, Node newParent) {
            removeNode(observedNode);
        }
    };
    
    /*
     * Get the specific cache
     */
    private static Map<Node, Boolean> getCache(Integer identifier) {
        Map<Node, Boolean> cache = isPhantomNodeCachePerCU.get(identifier);
        if (cache == null) {
            cache = synchronizedMap(new IdentityHashMap<>());
            isPhantomNodeCachePerCU.put(identifier,  cache);
            stats.put(identifier, new CacheStats());
//            System.out.println("Creating cache whith id "+identifier);
        }
        return cache;
    }
    
    /*
     * Remove a node from the CompilationUnit cache
     */
    private static void removeNode(Node node) {
        getCache(getCacheIdentifier(node)).remove(node);
    }
    
    /*
     * Return the cache identifier from the compilationUnit.hashCode() method or DEFAULT_CACHE_REGION identifier
     */
    private static Integer getCacheIdentifier(Node node) {
        Optional<CompilationUnit> cu = node.findCompilationUnit();
        return cu.isPresent() ? Integer.valueOf(cu.get().hashCode()) : DEFAULT_CACHE_REGION;
    }
    
    /*
     * Remove the cache entries corresponding to the node's CompilationUnit 
     */
    private static void removeCache(Node node) {
        Integer identifier = getCacheIdentifier(node);
        System.out.println(String.format("Removing cache %s, %s", identifier, stats.get(identifier).toString()));
        isPhantomNodeCachePerCU.remove(identifier);
    }

    static boolean isPhantomNode(Node node) {
        Integer identifier = getCacheIdentifier(node);
        Map<Node, Boolean> cache = getCache(identifier);
        if (cache.containsKey(node)) {
            stats.get(identifier).hit();
            return cache.get(node);
        } else {
            if (node instanceof UnknownType) {
                return true;
            }
            boolean res = (node.getParentNode().isPresent() 
                    && node.getParentNode().get().hasRange()
                    && node.hasRange()
                    && !node.getParentNode().get().getRange().get().contains(node.getRange().get())
                    || inPhantomNode(node, LEVELS_TO_EXPLORE));
            cache.put(node, res);
            node.register(cacheCleaner);
            stats.get(identifier).miss();
            return res;
        }
    }

    /**
     * A node contained in a phantom node is also a phantom node. We limit how many levels up we check just for performance reasons.
     */
    private static boolean inPhantomNode(Node node, int levels) {
        return node.getParentNode().isPresent() &&
                (isPhantomNode(node.getParentNode().get())
                        || inPhantomNode(node.getParentNode().get(), levels - 1));
    }

    /**
     * Clean up the cache used by the LexicalPreserving logic. This should only be used once you're done printing all parsed data with
     * a JavaParser's configuration setLexicalPreservationEnabled=true.
     * @deprecated @see cleanUpCache(CompilationUnit cu)
     */
    @Deprecated
    public static void cleanUpCache() {
        isPhantomNodeCache.clear();
    }
    
    /*
     * Allow to clean the phantom nodes cache linked to the specified CompilationUnit
     */
    public static void cleanUpCache(CompilationUnit cu) {
        removeCache(cu);
    }
    
    public static class CacheStats {
        int hits =0;
        int cachemiss = 0;
        
        public void hit() {
            hits++;
        }
        
        public void miss() {
            cachemiss++;
        }
        
        public String toString() {
            return String.format("hits=%s, cache miss=%s, efficiency=%s", hits, cachemiss, 100-((cachemiss*100)/hits));
        }
        
    }
}
