package issue1945.interfaces;

public abstract class HairTypeRenderer<T> {
	
	protected abstract void renderHair(T typeInstance, HairyAnimal animal);
	
	/**
	 * A proxy method casting the <code>typeInstance</code> parameter to the appropriate type for this renderer.
	 * This is necessary because the type that's retrieved by {@link HairyAnimal#getHairType()} is the generic {@link HairType} super interface.
	 */
	@SuppressWarnings("unchecked")
	public final void renderHair(HairType<?> typeInstance, HairyAnimal animal) {
		try {
			renderHair((T)typeInstance, animal);
		} catch (ClassCastException e) {
			throw new IllegalStateException("Renderer type and instance type don't match", e);
		}
	}
	
}
