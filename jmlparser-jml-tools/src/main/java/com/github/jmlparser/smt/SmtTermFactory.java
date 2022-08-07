package com.github.jmlparser.smt;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.jmlparser.smt.model.SAtom;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SList;
import com.github.jmlparser.smt.model.SmtType;
import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import lombok.SneakyThrows;

import java.math.BigInteger;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class SmtTermFactory {
    public static final SmtTermFactory INSTANCE = new SmtTermFactory();

    private final Cache<String, SAtom> symbolAndValueCache = CacheBuilder.newBuilder().softValues().build();

    //region boolean operators
    public SExpr and(SExpr... terms) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "and", terms);
    }

    public SExpr and(List<SExpr> seq) {
        return and(seq.toArray(new SExpr[0]));
    }

    public SExpr or(SExpr... terms) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "or", terms);
    }

    public SExpr impl(SExpr premise, SExpr concl) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "=>", premise, concl);

    }
    //endregion

    public SExpr ite(SExpr cond, SExpr then, SExpr otherwise) {
        return fnApply(then.getJavaType(), then.getSmtType(), "ite", cond, then, otherwise);
    }

    SExpr fnApply(ResolvedType javaType, SmtType smtType, String fn, SExpr arg) {
        return new SList(smtType, javaType, symbol(fn), arg);
    }

    private SExpr fnApply(ResolvedType javaType, SmtType smtType, String fn, SExpr arg1, SExpr arg2) {
        return new SList(smtType, javaType, symbol(fn), arg1, arg2);
    }

    private SExpr fnApply(ResolvedType javaType, SmtType smtType, String fn, SExpr arg1, SExpr arg2, SExpr arg3) {
        return new SList(smtType, javaType, symbol(fn), arg1, arg2, arg3);

    }

    private SExpr fnApply(ResolvedType javaType, SmtType smtType, String fn, SExpr... args) {
        return list(javaType, smtType, symbol(fn), args);
    }


    @SneakyThrows
    SAtom symbol(String fn) {
        return symbolAndValueCache.get(fn, () -> new SAtom(SmtType.SYMBOL, null, fn));
    }

    public SExpr forall(List<? extends SExpr> variables, SExpr formula) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "forall", list(variables), formula);
    }

    public SExpr exists(List<SExpr> variables, SExpr formula) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "exists", list(variables), formula);
    }


    SExpr list(ResolvedType javaType, SmtType smtType, SAtom symbol, SExpr[] args) {
        SExpr[] nargs = new SExpr[args.length + 1];
        nargs[0] = symbol;
        System.arraycopy(args, 0, nargs, 1, args.length);
        return new SList(smtType, javaType, nargs);
    }

    SExpr list(List<? extends SExpr> variables) {
        SExpr[] args = variables.toArray(new SExpr[0]);
        return new SList(null, null, args);
    }

    //region polymorphic operators
    public SExpr bor(SExpr left, SExpr right) {
        if (isBool(left, right)) return or(left, right);
        if (isBv(left, right)) return bvor(left, right);
        return typeException();
    }


    public SExpr add(SExpr left, SExpr right) {
        if (isInt(left, right)) return iadd(left, right);
        if (isBv(left, right)) return bvadd(left, right);
        return typeException();
    }

    public SExpr subtract(SExpr left, SExpr right) {
        if (isInt(left, right)) return isubstract(left, right);
        if (isBv(left, right)) return bvsubstract(left, right);
        return typeException();
    }

    public SExpr modulo(SExpr left, SExpr right, boolean b) {
        if (isInt(left, right)) return imodulo(left, right);
        if (isBv(left, right)) return bvmodulo(left, right);
        return typeException();
    }

    public SExpr shiftLeft(SExpr left, SExpr right) {
        if (isBv(left, right)) return bvshiftLeft(left, right);
        return typeException();
    }


    public SExpr shiftRight(SExpr left, SExpr right, boolean sign) {
        if (isBv(left, right)) return bvshiftRight(left, right, sign);
        return typeException();
    }

    public SExpr lessOrEquals(SExpr left, SExpr right, boolean sign) {
        if (isInt(left, right)) return ilessOrEquals(left, right);
        if (isBv(left, right)) return bvlessOrEquals(left, right);
        return typeException("Could not handle types '%s <= %s'", left.getSmtType(), right.getSmtType());
    }

    public SExpr greaterOrEquals(SExpr left, SExpr right, boolean b) {
        if (isInt(left, right)) return igreaterOrEquals(left, right);
        if (isBv(left, right)) return bvgreaterOrEquals(left, right);
        return typeException();
    }

    public SExpr lessThan(SExpr left, SExpr right) {
        if (isInt(left, right)) return ilessThan(left, right);
        if (isBv(left, right)) return bvlessThan(left, right);
        return typeException("Could not handle types '%s <%s'", left.getSmtType(), right.getSmtType());
    }

    public SExpr equiv(SExpr left, SExpr right) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "=", left, right);
    }

    public SExpr not(SExpr expr) {
        if (isBv(expr)) return bvnot(expr);
        if (isBool(expr)) return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "not", expr);
        return typeException();
    }


    public SExpr xor(SExpr left, SExpr right) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "xor", left, right);
    }

    public SExpr equality(SExpr left, SExpr right) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, "=", left, right);
    }

    public SExpr band(SExpr left, SExpr right) {
        if (isBool(left, right)) return and(left, right);

        if (isBv(left, right)) return bvand(left, right);

        return typeException();
    }


    private SExpr fnApplyToBool(String symbol, SExpr left, SExpr right) {
        return fnApply(ResolvedPrimitiveType.BOOLEAN, SmtType.BOOL, symbol, left, right);
    }

    public SExpr greaterThan(SExpr left, SExpr right) {
        if (isInt(left, right)) return igreaterThan(left, right);
        if (isBv(left, right)) return bvgreaterThan(left, right);
        return typeException("Could not handle types '%s > %s'", left.getSmtType(), right.getSmtType());
    }


    public SExpr negate(SExpr sexpr) {
        if (isBool(sexpr)) return not(sexpr);
        if (isBv(sexpr)) return bvnegate(sexpr);
        return typeException();
    }


    public SExpr multiply(SExpr left, SExpr right) {
        if (isInt(left, right)) return imultiply(left, right);
        if (isBv(left, right)) return bvmultiply(left, right);
        return typeException();
    }

    public SExpr divide(SExpr left, SExpr right, boolean b) {
        if (isInt(left, right)) return idivide(left, right);
        if (isBv(left, right)) return bvdivide(left, right);
        return typeException();
    }


    //endregion

    //region integer operations


    @SneakyThrows
    SAtom intValue(String svalue) {
        return symbolAndValueCache.get(svalue, () -> new SAtom(SmtType.INT, ResolvedPrimitiveType.INT, svalue));
    }

    @SneakyThrows
    SAtom intValue(long value) {
        return intValue("" + value);
    }

    @SneakyThrows
    SAtom intValue(BigInteger value) {
        return intValue("" + value);
    }

    public SExpr iadd(SExpr left, SExpr right) {
        return fnApplyToInt("+", left, right);
    }

    public SExpr ilessThan(SExpr left, SExpr right) {
        return fnApplyToBool("<", left, right);
    }

    public SExpr ilessOrEquals(SExpr left, SExpr right) {
        return fnApplyToBool("<=", left, right);
    }

    public SExpr igreaterThan(SExpr left, SExpr right) {
        return fnApplyToBool(">", left, right);
    }

    public SExpr igreaterOrEquals(SExpr left, SExpr right) {
        return fnApplyToBool(">=", left, right);
    }

    public SExpr isubstract(SExpr left, SExpr right) {
        return fnApplyToInt("-", left, right);
    }

    public SExpr imultiply(SExpr left, SExpr right) {
        return fnApplyToInt("*", left, right);
    }

    public SExpr intType() {
        return symbol("Int");
    }

    public SExpr imodulo(SExpr left, SExpr right) {
        return fnApplyToInt("mod", left, right);
    }

    public SExpr idivide(SExpr left, SExpr right) {
        return fnApplyToInt("/", left, right);
    }

    //endregion

    //region bit vectors
    public SExpr bvor(SExpr left, SExpr right) {
        return fnApplyToBV("bvor", left, right);
    }

    public SExpr bvnot(SExpr expr) {
        return fnApplyToBV("bvnot", expr);
    }

    public SExpr bvnegate(SExpr sexpr) {
        return fnApplyToBV("bvneg", sexpr);
    }

    public SExpr bvlessThan(SExpr left, SExpr right) {
        return fnApplyToBool("bvslt", left, right);
    }

    public SExpr bvlessOrEquals(SExpr left, SExpr right) {
        return fnApplyToBool("bvsle", left, right);
    }

    public SExpr bvgreaterThan(SExpr left, SExpr right) {
        return fnApplyToBool("bvsgt", left, right);
    }

    public SExpr bvgreaterOrEquals(SExpr left, SExpr right) {
        return fnApplyToBool("bvsge", left, right);
    }

    public SExpr bvshiftRight(SExpr left, SExpr right, boolean sign) {
        return fnApplyToBV(sign ? "bvashr" : "bvshr", left, right);
    }

    public SExpr bvshiftLeft(SExpr left, SExpr right) {
        return fnApplyToBV("bvshl", left, right);
    }

    public SExpr bvand(SExpr left, SExpr right) {
        return fnApplyToBV("bvand", left, right);
    }

    public SExpr bvadd(SExpr left, SExpr right) {
        return fnApplyToBV("bvadd", left, right);

    }

    private SExpr bvsubstract(SExpr left, SExpr right) {
        return fnApplyToBV("bvsub", left, right);
    }

    private SExpr bvmultiply(SExpr left, SExpr right) {
        return fnApplyToBV("bvmul", left, right);

    }

    private SExpr bvdivide(SExpr left, SExpr right) {
        return fnApplyToBV("bvsdiv", left, right);
    }

    private SExpr bvmodulo(SExpr left, SExpr right) {
        return fnApplyToBV("bvsrem", left, right);
    }

    private SExpr fnApplyToBV(String symbol, SExpr left) {
        return fnApply(null, left.getSmtType(), symbol, left);
    }


    public SExpr makeBitvector(int width, long value) {
        SmtType.BitVec type = SmtType.getBitVec(width);
        return new SList(type, null, symbol("_"), symbol("bv" + width), intValue(value));
    }


    public SExpr makeBitvector(int width, BigInteger value) {
        SmtType.BitVec type = SmtType.getBitVec(width);
        return new SList(type, null, symbol("_"), symbol("bv" + width), intValue(value));
    }


    public SExpr bvType(int width) {
        return new SList(SmtType.TYPE, null, symbol("_"), symbol("BitVec"), intValue(width));
    }
    //endregion

    private boolean isBool(SExpr sexpr) {
        return sexpr.getSmtType() == SmtType.BOOL;
    }

    private boolean isBool(SExpr left, SExpr right) {
        return left.getSmtType() == right.getSmtType() && isBool(left);
    }

    private boolean isBv(SExpr left, SExpr right) {
        return left.getSmtType() == right.getSmtType() && isBv(left);
    }

    private boolean isBv(SExpr left) {
        return left.getSmtType() instanceof SmtType.BitVec;
    }

    private boolean isInt(SExpr left, SExpr right) {
        return left.getSmtType() == right.getSmtType() && isInt(left);
    }

    private boolean isInt(SExpr left) {
        return left.getSmtType() == SmtType.INT;
    }

    private SExpr typeException() {
        throw new RuntimeException("Type mismatch!");
    }


    private SExpr fnApplyToInt(String symbol, SExpr left, SExpr right) {
        return fnApply(ResolvedPrimitiveType.INT, SmtType.INT, symbol, left, right);
    }

    private SExpr fnApplyToBV(String symbol, SExpr left, SExpr right) {
        return fnApply(null, left.getSmtType(), symbol, left, right);
    }


    public SExpr fpType(int width) {
        return new SList(SmtType.TYPE, null, symbol("_"), symbol("FloatingPoint"), intValue(width));
    }

    public SExpr arrayType(SExpr from, SExpr to) {
        return new SList(SmtType.TYPE, null, symbol("Array"), from, to);
    }


    public SExpr list(ResolvedType javaType, SmtType stype, Object... args) {
        SExpr[] nargs = new SExpr[args.length];
        for (int i = 0; i < args.length; i++) {
            Object arg = args[i];
            if (arg instanceof SExpr) nargs[i] = (SExpr) arg;
            else if (arg instanceof String) nargs[i] = symbol((String) arg);
            else typeException("Unhandled type %s", arg.getClass());
        }
        return new SList(stype, javaType, nargs);
    }

    public SExpr makeTrue() {
        return makeBoolean(true);
    }


    public SExpr makeFalse() {
        return makeBoolean(false);
    }

    @SneakyThrows
    public SExpr makeBoolean(boolean value) {
        String v = value ? "true" : "false";
        return symbolAndValueCache.get(v, () -> new SAtom(SmtType.BOOL, ResolvedPrimitiveType.BOOLEAN, v));
    }

    public SExpr makeInt(String value) {
        return intValue(value);
    }

    public SExpr makeNull() {
        return symbol("null");
    }

    public SExpr makeThis() {
        return symbol("this");
    }

    public SExpr makeSuper() {
        return symbol("super");
    }

    public SExpr boolType() {
        return symbol("Bool");
    }

    public SExpr javaObjectType() {
        return symbol("Object");
    }

    public SExpr type(SmtType type) {
        if (type == SmtType.JAVA_OBJECT) return javaObjectType();
        if (type == SmtType.INT) return intType();
        if (type == SmtType.REAL) return realType();
        if (type == SmtType.FP32) return fpType(32);
        if (type == SmtType.FP64) return fpType(64);
        if (type == SmtType.BOOL) return boolType();
        if (type instanceof SmtType.Array)
            return arrayType(type(((SmtType.Array) type).from), type(((SmtType.Array) type).to));
        if (type instanceof SmtType.BitVec) return bvType(((SmtType.BitVec) type).width);

        return typeException();
    }


    private SExpr realType() {
        return symbol("Int");
    }

    public SExpr var(SmtType type, ResolvedType javaType, String name) {
        //nocache, conflict in type could be created
        return new SAtom(type, javaType, name);
    }

    @SneakyThrows
    public SExpr command(String symbol, SExpr... args) {
        return fnApply(null, SmtType.COMMAND, symbol, args);
    }

    public SExpr select(SmtType stype, ResolvedType javaType, SExpr array, SExpr index) {
        return list(javaType, stype, symbol("select"), array, index);
    }

    public SExpr store(SExpr array, SExpr index, SExpr value) {
        return list(array.getJavaType(), array.getSmtType(), symbol("store"), array, index, value);
    }

    public SExpr fieldAccess(ResolvedType javaType, SmtType stype, String field, SExpr obj) {
        return fnApply(javaType, stype, field, obj);
    }

    private SExpr typeException(String fmt, Object... args) {
        throw new RuntimeException(String.format(fmt, args));
    }

    public SExpr let(List<SExpr> vars, SExpr body) {
        return list(body.getJavaType(), body.getSmtType(), "let", list(vars), body);
    }

    public SExpr nonNull(SExpr expr) {
        return not(equality(expr, makeNull()));
    }

    public SExpr binder(SmtType type, String name) {
        return list(null, null, name, type(type));
    }

}
