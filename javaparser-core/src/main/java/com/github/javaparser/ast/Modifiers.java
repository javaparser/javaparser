package com.github.javaparser.ast;

import javax.lang.model.element.Modifier;
import java.util.EnumSet;
import java.util.Set;

/**
 * @author Federico Tomassetti
 * @since 2.0.1
 */
public class Modifiers {

    private Set<Modifier> modifiers;
    
    public Modifiers(){
        this(EnumSet.noneOf(Modifier.class));
    }
    
    private Modifiers(Set<Modifier> modifiers) {
        this.modifiers = modifiers;
    }

    public boolean hasModifier(javax.lang.model.element.Modifier modifier) {
        return modifiers.contains(modifier);
    }

    public boolean hasAbstract() {
        return hasModifier(Modifier.ABSTRACT);
    }

    public boolean hasFinal() {
        return hasModifier(Modifier.FINAL);
    }

    public boolean hasNative() {
        return hasModifier(Modifier.NATIVE);
    }

    public boolean hasPrivate() {
        return hasModifier(Modifier.PRIVATE);
    }

    public boolean hasProtected() {
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
        return !hasPublic() && !hasProtected() && !hasPrivate();
    }

    public boolean hasPublic() {
        return hasModifier(Modifier.PUBLIC);
    }


    public boolean hasStatic() {
        return hasModifier(Modifier.STATIC);
    }


    public boolean hasStrictfp() {
        return hasModifier(Modifier.STRICTFP);
    }


    public boolean hasSynchronized() {
        return hasModifier(Modifier.SYNCHRONIZED);
    }


    public boolean hasTransient() {
        return hasModifier(Modifier.TRANSIENT);
    }


    public boolean hasVolatile() {
        return hasModifier(Modifier.VOLATILE);
    }

    public boolean has(Modifier modifier) {
        return modifiers.contains(modifier);
    }

    /**
     * Return a copy of this instance, with the given modifier set.
     * If the modifier is already set this is returned.
     */
    public Modifiers set(Modifier modifier) {
        if (modifiers.contains(modifier)) {
            return this;
        }
        Set<Modifier> newModifiers = EnumSet.copyOf(modifiers);
        newModifiers.add(modifier);
        return new Modifiers(newModifiers);
    }

    /**
     * Return a copy of this instance, with the given modifier unset.
     * If the modifier is already not set this is returned.
     */
    public Modifiers unset(Modifier modifier) {
        if (!modifiers.contains(modifier)) {
            return this;
        }
        Set<Modifier> newModifiers = EnumSet.copyOf(modifiers);
        newModifiers.remove(modifier);
        return new Modifiers(newModifiers);
    }

    public AccessSpecifier getAccessSpecifier() {
        if (hasPublic()){
            return AccessSpecifier.PUBLIC;
        } else if (hasProtected()){
            return AccessSpecifier.PROTECTED;
        } else if (hasPrivate()){
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }
}
