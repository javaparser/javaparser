package issue1945.implementations;
import issue1945.interfaces.HairType;

public class HairTypeWool implements HairType<WoolRenderer> {
	
	@Override
	public WoolRenderer getRenderer() {
		return WoolRenderer.INSTANCE;
	}
	
}
