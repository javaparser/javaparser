package me.tomassetti.symbolsolver.logic;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import javaslang.Tuple2;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeParameter;
import me.tomassetti.symbolsolver.model.typesystem.Type;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.easymock.EasyMock;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

public class GenericTypeInferenceLogicTest {

    @Test
    public void inferGenericTypesTestEmptyCase() {
        assertEquals(Collections.emptyMap(), GenericTypeInferenceLogic.inferGenericTypes(Collections.emptyList()));
    }

    @Test
    public void inferGenericTypesTestSimpleCase() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        me.tomassetti.symbolsolver.model.resolution.TypeParameter a = EasyMock.createMock(me.tomassetti.symbolsolver.model.resolution.TypeParameter.class);
        EasyMock.expect(a.getName()).andReturn("A").anyTimes();
        EasyMock.replay(a);
        TypeParameter aUsage = new TypeParameter(a);
        assertEquals(ImmutableMap.of("A", string), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(aUsage, string))));
    }

    @Test
    public void inferGenericTypesTestSimpleCaseWithTwoSubstitutions() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        ReferenceType object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        me.tomassetti.symbolsolver.model.resolution.TypeParameter a = EasyMock.createMock(me.tomassetti.symbolsolver.model.resolution.TypeParameter.class);
        me.tomassetti.symbolsolver.model.resolution.TypeParameter b = EasyMock.createMock(me.tomassetti.symbolsolver.model.resolution.TypeParameter.class);
        me.tomassetti.symbolsolver.model.resolution.TypeParameter c = EasyMock.createMock(me.tomassetti.symbolsolver.model.resolution.TypeParameter.class);
        EasyMock.expect(a.getName()).andReturn("A").anyTimes();
        EasyMock.expect(b.getName()).andReturn("B").anyTimes();
        EasyMock.expect(c.getName()).andReturn("C").anyTimes();
        EasyMock.replay(a);
        EasyMock.replay(b);
        EasyMock.replay(c);
        TypeParameter aUsage = new TypeParameter(a);
        TypeParameter bUsage = new TypeParameter(b);
        TypeParameter cUsage = new TypeParameter(c);
        assertEquals(ImmutableMap.of("A", string, "B", object, "C", string), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(aUsage, string),
                        new Tuple2<Type, Type>(bUsage, object),
                        new Tuple2<Type, Type>(cUsage, string))));
    }

    @Test
    public void inferGenericTypesTestSimpleCaseNoSubstitutions() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        ReferenceType object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        assertEquals(Collections.emptyMap(), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(object, string),
                        new Tuple2<Type, Type>(object, object),
                        new Tuple2<Type, Type>(object, string))));
    }
}
