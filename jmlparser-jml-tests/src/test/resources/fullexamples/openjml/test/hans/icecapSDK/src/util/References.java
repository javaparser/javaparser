package util;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;

public class References {

	@IcecapCVar
	static private Object reference;

	private static class ReferencesHelper {
		@IcecapCVar
		static private int reference;

		@IcecapCompileMe
		public static int getReference() {
			return reference;
		}
	}

	@IcecapCompileMe
	public static int getReference(Object obj) {
		reference = obj;
		return ReferencesHelper.getReference();
	}
}
