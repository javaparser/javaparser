package jml;

import java.util.BitSet;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author Alexander Weigl
 * @version 1 (2/2/20)
 * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_6.html#SEC41
 */
public class JmlSpecs {
    /*private Map<ParserRuleContext, Object> types = new HashMap<>();
    private List<ParserRuleContext>
            classInvariant, axioms, models, loopInvariant, commands;
*/
    private BitSet modifiers = new BitSet();

    public boolean hasModifier(int type) {
        return modifiers.get(type);
    }

    public void setModifier(int type, boolean b) {
        if (b) {
            modifiers.set(type);
        } else {
            modifiers.clear(type);
        }
    }

    private static final AtomicInteger modifierCounter = new AtomicInteger();
    public static final int MODIFIER_PUBLIC = modifierCounter.getAndIncrement();
    public static final int MODIFIER_PRIVATE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_PROTECTED = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SPEC_PUBLIC = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SPEC_PROTECTED = modifierCounter.getAndIncrement();
    public static final int MODIFIER_ABSTRACT = modifierCounter.getAndIncrement();
    public static final int MODIFIER_STATIC = modifierCounter.getAndIncrement();
    public static final int MODIFIER_INSTANCE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_MODEL = modifierCounter.getAndIncrement();
    public static final int MODIFIER_GHOST = modifierCounter.getAndIncrement();
    public static final int MODIFIER_PURE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_HELPER = modifierCounter.getAndIncrement();
    public static final int MODIFIER_FINAL = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SYNCHRONIZED = modifierCounter.getAndIncrement();
    public static final int MODIFIER_TRANSIENT = modifierCounter.getAndIncrement();
    public static final int MODIFIER_VOLATILE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_NATIVE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_STRICTFP = modifierCounter.getAndIncrement();
    public static final int MODIFIER_MONITORED = modifierCounter.getAndIncrement();
    public static final int MODIFIER_UNINITIALIZED = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SPEC_JAVA_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SPEC_SAFE_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_SPEC_BIGINT_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_CODE_JAVA_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_CODE_SAFE_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_CODE_BIGINT_MATH = modifierCounter.getAndIncrement();
    public static final int MODIFIER_NON_NULL = modifierCounter.getAndIncrement();
    public static final int MODIFIER_NULLABLE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_MODIFIER_NULLABLE_BY_DEFAULT = modifierCounter.getAndIncrement();
    public static final int MODIFIER_CODE = modifierCounter.getAndIncrement();
    public static final int MODIFIER_extract = modifierCounter.getAndIncrement();

    public static final int MODIFIER_PEER = modifierCounter.getAndIncrement();
    public static final int MODIFIER_REP = modifierCounter.getAndIncrement();
    public static final int MODIFIER_READONLY = modifierCounter.getAndIncrement();

}
