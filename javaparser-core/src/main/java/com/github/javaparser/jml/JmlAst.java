package jml;

import jdk.nashorn.internal.ir.annotations.Immutable;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.RequiredArgsConstructor;

/**
 * @author Alexander Weigl
 * @version 1 (6/1/20)
 */
@Data
public class JmlAst {
    private String filename;
    private int startOffset;
    private int endOffset;

    @Data
    @Immutable
    @Builder
    @AllArgsConstructor
    public static class Contract extends JmlAst {
        private int contractType;
    }


    @Data
    @Immutable
    @Builder
    @RequiredArgsConstructor
    @AllArgsConstructor
    public static class Expr extends JmlAst {
        private String returnType;
    }

    @Data
    @AllArgsConstructor
    public static class UnaryExpr extends Expr {
        private int operator;
        private Expr sub;
    }


    @Data
    @AllArgsConstructor
    public static class BinaryExpr extends Expr {
        private int operator;
        private Expr left;
        private Expr right;
    }

    @Data
    @AllArgsConstructor
    public static class IfThenElse extends Expr {
        private Expr cond, then, otherwise;
    }

    @Data
    @AllArgsConstructor
    public static class ArrayAccess extends Expr {
        private Expr left;
        private Expr index;
    }

    @Data
    @AllArgsConstructor
    public static class ArrayAccessAll extends Expr {
        private Expr left;
    }

    @Data
    @AllArgsConstructor
    public static class FieldAccess extends Expr {
        private Expr left, index;
    }
}
