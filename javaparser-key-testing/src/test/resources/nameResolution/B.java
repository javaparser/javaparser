class B {
    void m() {
        $methodFrame(source = setSize(int)@sub1.TestJavaCardDLExtensions){
            $methodFrame(source = setOther(int)@sub2.Other){
                Third four = new Third();
                int other2 = other;
            }
            TestJavaCardDLExtensions t = new TestJavaCardDLExtensions();
        }
    }
}

//? name: new TestJavaCardDLExtensions()@(line 8,col 42) refers to TestJavaCardDLExtensions@_
//? name: new Third()@(line 5,col 30) refers to Third@_
//? name: other@(line 6,col 30) refers to other@(line 4,col 5) in sub2/Other.java
//? type: new TestJavaCardDLExtensions()@(line 8,col 42) refers to ReferenceType{sub1.TestJavaCardDLExtensions, typeParametersMap=TypeParametersMap{nameToValue={}}}
//? type: new Third()@(line 5,col 30) refers to ReferenceType{sub2.Third, typeParametersMap=TypeParametersMap{nameToValue={}}}
//? type: other@(line 6,col 30) refers to PrimitiveTypeUsage{name='int'}