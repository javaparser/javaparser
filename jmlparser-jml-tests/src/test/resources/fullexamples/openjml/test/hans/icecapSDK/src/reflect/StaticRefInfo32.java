package reflect;

import icecaptools.IcecapCVar;

public class StaticRefInfo32 {
	@IcecapCVar(expression = "staticReferenceOffsets", requiredIncludes = "extern const uint32* staticReferenceOffsets;\n")
	static int staticReferenceOffsets;
	
	@IcecapCVar(expression = "classData", requiredIncludes = "extern const unsigned char* classData;\n")
	static int classData;
}
