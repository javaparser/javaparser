/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.AnnotationDefaultAttribute;
import javassist.bytecode.annotation.BooleanMemberValue;
import javassist.bytecode.annotation.CharMemberValue;
import javassist.bytecode.annotation.DoubleMemberValue;
import javassist.bytecode.annotation.IntegerMemberValue;
import javassist.bytecode.annotation.LongMemberValue;
import javassist.bytecode.annotation.MemberValue;
import javassist.bytecode.annotation.StringMemberValue;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
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

    public JavassistAnnotationMemberDeclaration(CtMethod annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
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
    public ResolvedType getType() {
        try {
            CtClass returnType = annotationMember.getReturnType();
            if (returnType.isPrimitive()) {
                return ResolvedPrimitiveType.byName(returnType.getName());
            }
            SymbolReference<ResolvedReferenceTypeDeclaration> rrtd = typeSolver.tryToSolveType(returnType.getName());
            if (rrtd.isSolved()) {
                return new ReferenceTypeImpl(rrtd.getCorrespondingDeclaration(), typeSolver);
            }
        } catch (NotFoundException e) {
            // nothing to do
        }
        throw new UnsupportedOperationException(String.format("Obtaining the type of the annotation member %s is not supported yet.", annotationMember.getLongName()));
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }

    @Override
    public Optional<AnnotationMemberDeclaration> toAst() {
        return Optional.empty();
    }
}
