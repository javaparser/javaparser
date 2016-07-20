Scenario: A compilationUnit in which we call 3 times setImport with 2 duplicates values

Given a compilation unit with 3 imports but 2 duplicates values
Then the compilation unit has 2 imports

Scenario: Check if 
	CompilationUnit:
	
    public ClassOrInterfaceDeclaration addClass(String name) {
    public ClassOrInterfaceDeclaration addClass(String name, EnumSet<Modifier> modifiers) {
    public ClassOrInterfaceDeclaration addInterface(String name) {
    public ClassOrInterfaceDeclaration addInterface(String name, EnumSet<Modifier> modifiers) {
    public EnumDeclaration addEnum(String name) {
    public EnumDeclaration addEnum(String name, EnumSet<Modifier> modifiers) {
    public AnnotationDeclaration addAnnotationDeclaration(String name) {
    public AnnotationDeclaration addAnnotationDeclaration(String name, EnumSet<Modifier> modifiers) {
    public ClassOrInterfaceDeclaration getClassByName(String className) {
    public ClassOrInterfaceDeclaration getInterfaceByName(String interfaceName) {
    public EnumDeclaration getEnumByName(String enumName) {
    public AnnotationDeclaration getAnnotationDeclarationByName(String annotationName) {
	
