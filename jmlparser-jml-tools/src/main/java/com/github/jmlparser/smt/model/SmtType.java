package com.github.jmlparser.smt.model;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.Map;

public class SmtType {
    public static final SmtType FP32 = new SmtType("(_ FloatingPoint 32)");
    public static final SmtType FP64 = new SmtType("(_ FloatingPoint 64)");
    public static final SmtType STRING = new SmtType("String");


    public static class BitVec extends SmtType {
        public final int width;

        BitVec(int width) {
            super("(_ BitVec " + width + ")");
            this.width = width;
        }
    }


    @Nonnull
    private static final Map<Integer, BitVec> bvCache = new HashMap<>(8);

    public static final SmtType COMMAND = new SmtType("_COMMAND_");
    public static final SmtType INT = new SmtType("Int");
    public static final SmtType REAL = new SmtType("Real");
    public static final SmtType BOOL = new SmtType("Bool");
    public static final SmtType BV8 = getBitVec(8);
    public static final SmtType BV16 = getBitVec(16);
    public static final SmtType BV32 = getBitVec(32);
    public static final SmtType BV64 = getBitVec(64);
    public static final SmtType SYMBOL = new SmtType("_SYMBOL_");
    public static final SmtType TYPE = new SmtType("_TYPE_");

    public static final SmtType JAVA_OBJECT = new SmtType("_TYPE_");


    private SmtType(String name) {
        this.name = name;
    }

    public static BitVec getBitVec(int width) {
        return bvCache.computeIfAbsent(width, BitVec::new);
    }

    private final String name;

    @Override
    public String toString() {
        return name;
    }

    public static class Array extends SmtType {
        public final SmtType from;
        public final SmtType to;

        public Array(SmtType intType, SmtType cType) {
            super("(Array " + intType.name + " " + cType.name + ")");
            this.from = intType;
            this.to = cType;
        }
    }
}
