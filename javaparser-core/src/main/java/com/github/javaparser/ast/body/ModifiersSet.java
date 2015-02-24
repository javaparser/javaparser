package com.github.javaparser.ast.body;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.NodeWithModifiers;

import javax.lang.model.element.Modifier;
import java.util.EnumSet;
import java.util.Set;

/**
 * @author Federico Tomassetti
 * @since 2.0.1
 */
public class ModifiersSet {

    private Set<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    public boolean hasModifier(javax.lang.model.element.Modifier modifier) {
        return modifiers.contains(modifier);
    }

    public boolean isAbstract() {
        return hasModifier(Modifier.ABSTRACT);
    }

    public boolean isFinal() {
        return hasModifier(Modifier.FINAL);
    }

    public boolean isNative() {
        return hasModifier(Modifier.NATIVE);
    }

    public boolean isPrivate() {
        return hasModifier(Modifier.PRIVATE);
    }

    public boolean isProtected() {
        return hasModifier(Modifier.PROTECTED);
    }

    /**
     * Is the element accessible from within the package?
     * It is the level of access which is applied if no modifiers are chosen,
     * it is sometimes called "default".
     *
     * @return true if modifier denotes package level access
     */
    public boolean hasPackageLevelAccess() {
        return !isPublic() && !isProtected() && !isPrivate();
    }

    public boolean isPublic() {
        return hasModifier(Modifier.PUBLIC);
    }


    public boolean isStatic() {
        return hasModifier(Modifier.STATIC);
    }


    public boolean isStrictfp() {
        return hasModifier(Modifier.STRICTFP);
    }


    public boolean isSynchronized() {
        return hasModifier(Modifier.SYNCHRONIZED);
    }


    public boolean isTransient() {
        return hasModifier(Modifier.TRANSIENT);
    }


    public boolean isVolatile() {
        return hasModifier(Modifier.VOLATILE);
    }

    public boolean has(Modifier modifier) {
        return modifiers.contains(modifier);
    }

    public void set(Modifier modifier) {
        modifiers.add(modifier);
    }

    public AccessSpecifier getAccessSpecifier() {
        if (isPublic()){
            return AccessSpecifier.PUBLIC;
        } else if (isProtected()){
            return AccessSpecifier.PROTECTED;
        } else if (isPrivate()){
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }
}
