/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.utils.ResolvedAnnotationsUtil;
import javassist.CtMethod;
import javassist.bytecode.AnnotationDefaultAttribute;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import javassist.bytecode.annotation.*;

import java.util.*;
import java.util.function.Function;

/**
 * @author Malte Skoruppa
 */
public class JavassistAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {
    
    private static Map<Class<? extends MemberValue>, Function<MemberValue, ? extends Expression>> memberValueAsExressionConverter = new HashMap<>();
    static {
        memberValueAsExressionConverter.put(BooleanMemberValue.class, (memberValue) -> new BooleanLiteralExpr(BooleanMemberValue.class.cast(memberValue).getValue()));
        memberValueAsExressionConverter.put(CharMemberValue.class, (memberValue) -> new CharLiteralExpr(CharMemberValue.class.cast(memberValue).getValue()));
        memberValueAsExressionConverter.put(DoubleMemberValue.class, (memberValue) -> new DoubleLiteralExpr(DoubleMemberValue.class.cast(memberValue).getValue()));
        memberValueAsExressionConverter.put(IntegerMemberValue.class, (memberValue) -> new IntegerLiteralExpr(IntegerMemberValue.class.cast(memberValue).getValue()));
        memberValueAsExressionConverter.put(LongMemberValue.class, (memberValue) -> new LongLiteralExpr(LongMemberValue.class.cast(memberValue).getValue()));
        memberValueAsExressionConverter.put(StringMemberValue.class, (memberValue) -> new StringLiteralExpr(StringMemberValue.class.cast(memberValue).getValue()));
    }

    private CtMethod annotationMember;
    private TypeSolver typeSolver;

    private ResolvedTypeParametrizable container;

    public JavassistAnnotationMemberDeclaration(CtMethod annotationMember, TypeSolver typeSolver, ResolvedTypeParametrizable container) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
        this.container = container;
    }

    @Override
    public Expression getDefaultValue() {
         AnnotationDefaultAttribute defaultAttribute = (AnnotationDefaultAttribute) annotationMember.getMethodInfo().getAttribute(AnnotationDefaultAttribute.tag);
         if (defaultAttribute == null) return null;
         MemberValue memberValue = defaultAttribute.getDefaultValue();
         Function<MemberValue, ? extends Expression> fn = memberValueAsExressionConverter.get(memberValue.getClass());
         if (fn == null) throw new UnsupportedOperationException(String.format("Obtaining the type of the annotation member %s is not supported yet.", annotationMember.getName()));
         return fn.apply(memberValue);
    }

    @Override
    public Optional<Object> getComputedDefaultValue() {
        AnnotationDefaultAttribute defaultAttribute = (AnnotationDefaultAttribute) annotationMember.getMethodInfo().getAttribute(AnnotationDefaultAttribute.tag);
        if (defaultAttribute == null) return Optional.empty();
        MemberValue memberValue = defaultAttribute.getDefaultValue();
        return Optional.of(JavassistUtils.computeMemberValue(memberValue, typeSolver));
    }

    @Override
    public ResolvedType getType() {
        try {
            String descriptor = annotationMember.getMethodInfo().getDescriptor();
            SignatureAttribute.MethodSignature signature = SignatureAttribute.toMethodSignature(descriptor);
            return JavassistUtils.signatureTypeToType(signature.getReturnType(), typeSolver, container);
        } catch (BadBytecode e) {
            // We don't expect this to happen, but we handle it anyway.
            throw new IllegalStateException("An invalid descriptor was received from JavaAssist.", e);
        }
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }

    @Override
    public List<? extends ResolvedAnnotation> getAnnotations() {
        return ResolvedAnnotationsUtil.getAnnotations(annotationMember, typeSolver);
    }

    @Override
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return ResolvedAnnotationsUtil.getDeclaredAnnotations(annotationMember, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavassistAnnotationMemberDeclaration that = (JavassistAnnotationMemberDeclaration) o;

        return annotationMember.equals(that.annotationMember);
    }

    @Override
    public int hashCode() {
        return annotationMember.hashCode();
    }
}
