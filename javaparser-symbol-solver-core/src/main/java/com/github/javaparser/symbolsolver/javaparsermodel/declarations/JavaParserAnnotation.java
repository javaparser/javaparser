/*
 *
 *  * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 *  * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *  *
 *  * This file is part of JavaParser.
 *  *
 *  * JavaParser can be used either under the terms of
 *  * a) the GNU Lesser General Public License as published by
 *  *     the Free Software Foundation, either version 3 of the License, or
 *  *     (at your option) any later version.
 *  * b) the terms of the Apache License
 *  *
 *  * You should have received a copy of both licenses in LICENCE.LGPL and
 *  * LICENCE.APACHE. Please refer to those files for details.
 *  *
 *  * JavaParser is distributed in the hope that it will be useful,
 *  * but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  * GNU Lesser General Public License for more details.
 *
 */

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.logic.AbstractAnnotation;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.utils.JavaParserConstantValueEvaluationUtil.evaluateConstantExpression;

public class JavaParserAnnotation extends AbstractAnnotation implements AssociableToAST {

    private AnnotationExpr wrappedNode;

    private TypeSolver typeSolver;

    public JavaParserAnnotation(AnnotationExpr wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Optional<Node> toAst() {
        return Optional.ofNullable(wrappedNode);
    }

    @Override
    protected ResolvedAnnotationDeclaration calculateAnnotationType() {
        return wrappedNode.resolve();
    }

    @Override
    public Map<ResolvedAnnotationMemberDeclaration, Object> getAnnotationMemberValueMap() {
        Map<ResolvedAnnotationMemberDeclaration, Object> tempMap = new HashMap<>();

        ResolvedAnnotationDeclaration tempAnnotationType = getAnnotationType();
        if (wrappedNode.isSingleMemberAnnotationExpr()) {
            SingleMemberAnnotationExpr tempSingleMember = wrappedNode.asSingleMemberAnnotationExpr();

            Optional<ResolvedAnnotationMemberDeclaration> tempAnnotationMember = tempAnnotationType.getAnnotationMembers()
                    .stream()
                    .filter(it -> Objects.equals(it.getName(), "value"))
                    .findFirst();

            tempAnnotationMember.ifPresent(it -> tempMap.put(it, evaluateConstantExpression(tempSingleMember.getMemberValue(), typeSolver, it.getType())));
        } else if (wrappedNode.isNormalAnnotationExpr()) {
            NormalAnnotationExpr tempNormalAnnotation = wrappedNode.asNormalAnnotationExpr();
            for (MemberValuePair tempPair : tempNormalAnnotation.getPairs()) {
                Optional<ResolvedAnnotationMemberDeclaration> tempAnnotationMember = tempAnnotationType.getAnnotationMembers()
                        .stream()
                        .filter(it -> Objects.equals(it.getName(), tempPair.getNameAsString()))
                        .findFirst();

                tempAnnotationMember.ifPresent(it -> tempMap.put(it, evaluateConstantExpression(tempPair.getValue(), typeSolver, it.getType())));
            }
        }
        return tempMap;
    }

    //
    /// Public methods: from Object
    ///

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserAnnotation that = (JavaParserAnnotation) o;

        return wrappedNode.equals(that.wrappedNode);
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }
}
