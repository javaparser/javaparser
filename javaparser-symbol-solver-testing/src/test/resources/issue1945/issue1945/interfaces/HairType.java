package issue1945.interfaces;

public interface HairType<R extends HairTypeRenderer<?>> {
	
	R getRenderer();
	
}
