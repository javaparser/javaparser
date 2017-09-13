package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ConstructorDeclaration;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;

import static java.util.Collections.unmodifiableList;
import static java.util.stream.Collectors.toCollection;
import static java.util.stream.Collectors.toList;

public interface NodeWithConstructors<N extends Node> extends NodeWithSimpleName<N>, NodeWithMembers<N> {
    /**
     * Try to find a {@link ConstructorDeclaration} with no parameters by its name
     *
     * @return the constructors found (multiple in case of polymorphism)
     */
    default Optional<ConstructorDeclaration> getDefaultConstructor() {
        return getMembers().stream().filter(bd -> bd instanceof ConstructorDeclaration).map(bd -> (ConstructorDeclaration) bd).filter(cd -> cd.getParameters().isEmpty()).findFirst();
    }

    /**
     * Adds a constructor to this
     *
     * @param modifiers the modifiers like {@link Modifier#PUBLIC}
     * @return the created constructor
     */
    default ConstructorDeclaration addConstructor(Modifier... modifiers) {
        ConstructorDeclaration constructorDeclaration = new ConstructorDeclaration();
        constructorDeclaration.setModifiers(Arrays.stream(modifiers).collect(toCollection(() -> EnumSet.noneOf(Modifier.class))));
        constructorDeclaration.setName(getName());
        getMembers().add(constructorDeclaration);
        return constructorDeclaration;
    }

    /**
     * Find all constructors for this class.
     *
     * @return the constructors found. This list is immutable.
     */
    default List<ConstructorDeclaration> getConstructors() {
        return unmodifiableList(getMembers().stream().filter(m -> m instanceof ConstructorDeclaration).map(m -> (ConstructorDeclaration) m).collect(toList()));
    }

    /**
     * Try to find a {@link ConstructorDeclaration} by its parameters types
     *
     * @param paramTypes the types of parameters like "Map&lt;Integer,String&gt;","int" to match<br> void
     * foo(Map&lt;Integer,String&gt; myMap,int number)
     * @return the constructor found (multiple in case of overloading)
     */
    default Optional<ConstructorDeclaration> getConstructorByParameterTypes(String... paramTypes) {
        return getConstructors().stream().filter(m -> m.hasParametersOfType(paramTypes)).findFirst();
    }

    /**
     * Try to find a {@link ConstructorDeclaration} by its parameters types
     *
     * @param paramTypes the types of parameters like "Map&lt;Integer,String&gt;","int" to match<br> void
     * foo(Map&lt;Integer,String&gt; myMap,int number)
     * @return the constructors found (multiple in case of overloading)
     */
    default Optional<ConstructorDeclaration> getConstructorByParameterTypes(Class<?>... paramTypes) {
        return getConstructors().stream().filter(m -> m.hasParametersOfType(paramTypes)).findFirst();
    }

}
