package icecaptools;

public @interface IcecapCFunc {
    String signature() default "";
    String requiredIncludes() default "";
    String hasReturnValue() default "false";
}
