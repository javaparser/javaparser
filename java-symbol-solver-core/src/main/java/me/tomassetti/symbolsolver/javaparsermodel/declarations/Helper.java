package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Modifier;
import me.tomassetti.symbolsolver.model.declarations.AccessLevel;

import java.util.EnumSet;

/**
 * @author Federico Tomassetti
 */
class Helper {

    public static AccessLevel toAccessLevel(EnumSet<Modifier> modifiers) {
        if (modifiers.contains(Modifier.PRIVATE)) {
            return AccessLevel.PRIVATE;
        } else if (modifiers.contains(Modifier.PROTECTED)) {
            return AccessLevel.PROTECTED;
        } else if (modifiers.contains(Modifier.PUBLIC)) {
            return AccessLevel.PUBLIC;
        } else {
            return AccessLevel.PACKAGE_PROTECTED;
        }
    }
}
