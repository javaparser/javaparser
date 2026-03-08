package issue1945.implementations;
import issue1945.interfaces.HairTypeRenderer;
import issue1945.interfaces.HairyAnimal;

public class WoolRenderer extends HairTypeRenderer<HairTypeWool> {
	
	public final static WoolRenderer INSTANCE = new WoolRenderer();
	
	private WoolRenderer() {
		//I'm a singleton
	}
	
	@Override
	public void renderHair(HairTypeWool type, HairyAnimal animal) {
		//... snip ...
	}
	
}
