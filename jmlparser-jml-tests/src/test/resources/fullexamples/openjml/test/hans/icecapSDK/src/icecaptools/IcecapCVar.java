package icecaptools;

public @interface IcecapCVar {
	String expression() default "";
	String requiredIncludes() default "";
}
