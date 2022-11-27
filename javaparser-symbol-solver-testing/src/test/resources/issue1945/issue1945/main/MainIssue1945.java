package issue1945.main;

import issue1945.implementations.Sheep;
import issue1945.interfaces.HairType;
import issue1945.interfaces.HairTypeRenderer;
import issue1945.interfaces.HairyAnimal;

public class MainIssue1945 {
	
	private final HairyAnimal sheep = new Sheep();
	
	public void chokes() {
		sheep.getHairType().getRenderer().renderHair(sheep.getHairType(), sheep);
	}
	
	public void chokes2() {
		HairType<?> hairType = sheep.getHairType();
		hairType.getRenderer().renderHair(hairType, sheep);
	}
	
	public void chokes3() {
		HairType<?> hairType = sheep.getHairType();
		hairType.getRenderer().renderHair(sheep.getHairType(), sheep);
	}
	
	
	
	
	
	public void works() {
		HairType<?> hairType = sheep.getHairType();
		HairTypeRenderer<?> hairTypeRenderer = hairType.getRenderer();
		
		hairTypeRenderer.renderHair(hairType, sheep);
	}
	
	public void works2() {
		HairTypeRenderer<?> hairTypeRenderer = sheep.getHairType().getRenderer();
		hairTypeRenderer.renderHair(sheep.getHairType(), sheep);
	}
	
	public void works3() {
		HairType<?> hairType = sheep.getHairType();
		HairTypeRenderer<?> hairTypeRenderer = hairType.getRenderer();
		
		hairTypeRenderer.renderHair(sheep.getHairType(), sheep);
	}
}
