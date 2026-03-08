package issue1945.implementations;
import issue1945.interfaces.HairType;
import issue1945.interfaces.HairyAnimal;

public class Sheep implements HairyAnimal {
	
	@Override
	public HairType<?> getHairType() {
		//simplified
		return new HairTypeWool();
	}
	
}
