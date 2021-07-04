package reflect;

import icecaptools.IcecapCVar;

public class StaticRefInfo64 {
	@IcecapCVar(expression = "staticReferenceOffsets", requiredIncludes = "extern const uint32* staticReferenceOffsets;\n")
	static long staticReferenceOffsets;
	
	@IcecapCVar(expression = "classData", requiredIncludes = "extern const unsigned char* classData;\n")
	static long classData;
}
