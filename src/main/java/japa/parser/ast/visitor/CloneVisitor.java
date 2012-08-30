package japa.parser.ast.visitor;

import java.util.ArrayList;
import java.util.List;

import japa.parser.ast.BlockComment;
import japa.parser.ast.Comment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.LineComment;
import japa.parser.ast.Node;
import japa.parser.ast.PackageDeclaration;
import japa.parser.ast.TypeParameter;
import japa.parser.ast.body.AnnotationDeclaration;
import japa.parser.ast.body.AnnotationMemberDeclaration;
import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import japa.parser.ast.body.EmptyMemberDeclaration;
import japa.parser.ast.body.EmptyTypeDeclaration;
import japa.parser.ast.body.EnumConstantDeclaration;
import japa.parser.ast.body.EnumDeclaration;
import japa.parser.ast.body.FieldDeclaration;
import japa.parser.ast.body.InitializerDeclaration;
import japa.parser.ast.body.JavadocComment;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.expr.ArrayAccessExpr;
import japa.parser.ast.expr.ArrayCreationExpr;
import japa.parser.ast.expr.ArrayInitializerExpr;
import japa.parser.ast.expr.AssignExpr;
import japa.parser.ast.expr.BinaryExpr;
import japa.parser.ast.expr.BooleanLiteralExpr;
import japa.parser.ast.expr.CastExpr;
import japa.parser.ast.expr.CharLiteralExpr;
import japa.parser.ast.expr.ClassExpr;
import japa.parser.ast.expr.ConditionalExpr;
import japa.parser.ast.expr.DoubleLiteralExpr;
import japa.parser.ast.expr.EnclosedExpr;
import japa.parser.ast.expr.Expression;
import japa.parser.ast.expr.FieldAccessExpr;
import japa.parser.ast.expr.InstanceOfExpr;
import japa.parser.ast.expr.IntegerLiteralExpr;
import japa.parser.ast.expr.IntegerLiteralMinValueExpr;
import japa.parser.ast.expr.LongLiteralExpr;
import japa.parser.ast.expr.LongLiteralMinValueExpr;
import japa.parser.ast.expr.MarkerAnnotationExpr;
import japa.parser.ast.expr.MemberValuePair;
import japa.parser.ast.expr.MethodCallExpr;
import japa.parser.ast.expr.NameExpr;
import japa.parser.ast.expr.NormalAnnotationExpr;
import japa.parser.ast.expr.NullLiteralExpr;
import japa.parser.ast.expr.ObjectCreationExpr;
import japa.parser.ast.expr.QualifiedNameExpr;
import japa.parser.ast.expr.SingleMemberAnnotationExpr;
import japa.parser.ast.expr.StringLiteralExpr;
import japa.parser.ast.expr.SuperExpr;
import japa.parser.ast.expr.ThisExpr;
import japa.parser.ast.expr.UnaryExpr;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.AssertStmt;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.BreakStmt;
import japa.parser.ast.stmt.CatchClause;
import japa.parser.ast.stmt.ContinueStmt;
import japa.parser.ast.stmt.DoStmt;
import japa.parser.ast.stmt.EmptyStmt;
import japa.parser.ast.stmt.ExplicitConstructorInvocationStmt;
import japa.parser.ast.stmt.ExpressionStmt;
import japa.parser.ast.stmt.ForStmt;
import japa.parser.ast.stmt.ForeachStmt;
import japa.parser.ast.stmt.IfStmt;
import japa.parser.ast.stmt.LabeledStmt;
import japa.parser.ast.stmt.ReturnStmt;
import japa.parser.ast.stmt.Statement;
import japa.parser.ast.stmt.SwitchEntryStmt;
import japa.parser.ast.stmt.SwitchStmt;
import japa.parser.ast.stmt.SynchronizedStmt;
import japa.parser.ast.stmt.ThrowStmt;
import japa.parser.ast.stmt.TryStmt;
import japa.parser.ast.stmt.TypeDeclarationStmt;
import japa.parser.ast.stmt.WhileStmt;
import japa.parser.ast.type.ClassOrInterfaceType;
import japa.parser.ast.type.PrimitiveType;
import japa.parser.ast.type.ReferenceType;
import japa.parser.ast.type.Type;
import japa.parser.ast.type.VoidType;
import japa.parser.ast.type.WildcardType;

public class CloneVisitor implements GenericVisitor<Node, Object> {

	@Override
	public Node visit(CompilationUnit _n, Object _arg) {
		PackageDeclaration package_ = cloneNodes(_n.getPackage(), _arg);
		List<ImportDeclaration> imports = visit(_n.getImports(), _arg);
		List<TypeDeclaration> types = visit(_n.getTypes(), _arg);
		List<Comment> comments = visit(_n.getComments(), _arg);

		return new CompilationUnit(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				package_, imports, types, comments
		);
	}

	@Override
	public Node visit(PackageDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		NameExpr name = cloneNodes(_n.getName(), _arg);

		return new PackageDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				annotations, name
		);
	}

	@Override
	public Node visit(ImportDeclaration _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);

		return new ImportDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, _n.isStatic(), _n.isAsterisk()
		);
	}

	@Override
	public Node visit(TypeParameter _n, Object _arg) {
		List<ClassOrInterfaceType> typeBound = visit(_n.getTypeBound(), _arg);

		return new TypeParameter(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), typeBound
		);
	}

	@Override
	public Node visit(LineComment _n, Object _arg) {
		return new LineComment(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getContent()
		);
	}

	@Override
	public Node visit(BlockComment _n, Object _arg) {
		return new BlockComment(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getContent()
		);
	}

	@Override
	public Node visit(ClassOrInterfaceDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<ClassOrInterfaceType> extendsList = visit(_n.getExtends(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		return new ClassOrInterfaceDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, _n.isInterface(), _n.getName(),
				typeParameters, extendsList, implementsList, members
		);
	}

	@Override
	public Node visit(EnumDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<EnumConstantDeclaration> entries = visit(_n.getEntries(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		return new EnumDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, _n.getName(), implementsList, entries, members
		);
	}

	@Override
	public Node visit(EmptyTypeDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);

		return new EmptyTypeDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc
		);
	}

	@Override
	public Node visit(EnumConstantDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> classBody = visit(_n.getClassBody(), _arg);

		return new EnumConstantDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, annotations, _n.getName(), args, classBody
		);
	}

	@Override
	public Node visit(AnnotationDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);

		return new AnnotationDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, _n.getName(), members
		);
	}

	@Override
	public Node visit(AnnotationMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression defaultValue = cloneNodes(_n.getDefaultValue(), _arg);

		return new AnnotationMemberDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, type_, _n.getName(), defaultValue
		);
	}

	@Override
	public Node visit(FieldDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> variables = visit(_n.getVariables(), _arg);

		return new FieldDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, type_, variables
		);
	}

	@Override
	public Node visit(VariableDeclarator _n, Object _arg) {
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Expression init = cloneNodes(_n.getInit(), _arg);

		return new VariableDeclarator(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				id, init
		);
	}

	@Override
	public Node visit(VariableDeclaratorId _n, Object _arg) {
		return new VariableDeclaratorId(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), _n.getArrayCount()
		);
	}

	@Override
	public Node visit(ConstructorDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<Parameter> parameters = visit(_n.getParameters(), _arg);
		List<NameExpr> throws_ = visit(_n.getThrows(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		return new ConstructorDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, typeParameters, _n.getName(), parameters, throws_, block
		);
	}

	@Override
	public Node visit(MethodDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Parameter> parameters = visit(_n.getParameters(), _arg);
		List<NameExpr> throws_ = visit(_n.getThrows(), _arg);
		BlockStmt block = cloneNodes(_n.getBody(), _arg);

		return new MethodDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.getModifiers(), annotations, typeParameters, type_, _n.getName(),
				parameters, _n.getArrayCount(), throws_, block
		);
	}

	@Override
	public Node visit(Parameter _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);

		return new Parameter(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, type_, _n.isVarArgs(), id
		);
	}

	@Override
	public Node visit(EmptyMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);

		return new EmptyMemberDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc
		);
	}

	@Override
	public Node visit(InitializerDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		return new InitializerDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				javaDoc, _n.isStatic(), block
		);
	}

	@Override
	public Node visit(JavadocComment _n, Object _arg) {
		return new JavadocComment(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getContent()
		);
	}

	@Override
	public Node visit(ClassOrInterfaceType _n, Object _arg) {
		ClassOrInterfaceType scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);

		return new ClassOrInterfaceType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, _n.getName(), typeArgs
		);
	}

	@Override
	public Node visit(PrimitiveType _n, Object _arg) {
		return new PrimitiveType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getType()
		);
	}

	@Override
	public Node visit(ReferenceType _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);

		return new ReferenceType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, _n.getArrayCount()
		);
	}

	@Override
	public Node visit(VoidType _n, Object _arg) {
		return new VoidType(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
	}

	@Override
	public Node visit(WildcardType _n, Object _arg) {
		ReferenceType ext = cloneNodes(_n.getExtends(), _arg);
		ReferenceType sup = cloneNodes(_n.getSuper(), _arg);

		return new WildcardType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				ext, sup
		);
	}

	@Override
	public Node visit(ArrayAccessExpr _n, Object _arg) {
		Expression name = cloneNodes(_n.getName(), _arg);
		Expression index = cloneNodes(_n.getIndex(), _arg);

		return new ArrayAccessExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, index
		);
	}

	@Override
	public Node visit(ArrayCreationExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Expression> dimensions = visit(_n.getDimensions(), _arg);

		ArrayCreationExpr r = new ArrayCreationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, dimensions, _n.getArrayCount()
		);
		if (_n.getInitializer() != null) // ArrayCreationExpr has two mutually exclusive constructors
			r.setInitializer(cloneNodes(_n.getInitializer(), _arg));
		return r;
	}

	@Override
	public Node visit(ArrayInitializerExpr _n, Object _arg) {
		List<Expression> values = visit(_n.getValues(), _arg);

		return new ArrayInitializerExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				values
		);
	}

	@Override
	public Node visit(AssignExpr _n, Object _arg) {
		Expression target = cloneNodes(_n.getTarget(), _arg);
		Expression value = cloneNodes(_n.getValue(), _arg);

		return new AssignExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				target, value, _n.getOperator()
		);
	}

	@Override
	public Node visit(BinaryExpr _n, Object _arg) {
		Expression left = cloneNodes(_n.getLeft(), _arg);
		Expression right = cloneNodes(_n.getRight(), _arg);

		return new BinaryExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				left, right, _n.getOperator()
		);
	}

	@Override
	public Node visit(CastExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		return new CastExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, expr
		);
	}

	@Override
	public Node visit(ClassExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);

		return new ClassExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_
		);
	}

	@Override
	public Node visit(ConditionalExpr _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Expression thenExpr = cloneNodes(_n.getThenExpr(), _arg);
		Expression elseExpr = cloneNodes(_n.getElseExpr(), _arg);

		return new ConditionalExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, thenExpr, elseExpr
		);
	}

	@Override
	public Node visit(EnclosedExpr _n, Object _arg) {
		Expression inner = cloneNodes(_n.getInner(), _arg);

		return new EnclosedExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				inner
		);
	}

	@Override
	public Node visit(FieldAccessExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);

		return new FieldAccessExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, typeArgs, _n.getField()
		);
	}

	@Override
	public Node visit(InstanceOfExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);

		return new InstanceOfExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, type_
		);
	}

	@Override
	public Node visit(StringLiteralExpr _n, Object _arg) {
		return new StringLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(IntegerLiteralExpr _n, Object _arg) {
		return new IntegerLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(LongLiteralExpr _n, Object _arg) {
		return new LongLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(IntegerLiteralMinValueExpr _n, Object _arg) {
		return new IntegerLiteralMinValueExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
	}

	@Override
	public Node visit(LongLiteralMinValueExpr _n, Object _arg) {
		return new LongLiteralMinValueExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
	}

	@Override
	public Node visit(CharLiteralExpr _n, Object _arg) {
		return new CharLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(DoubleLiteralExpr _n, Object _arg) {
		return new DoubleLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(BooleanLiteralExpr _n, Object _arg) {
		return new BooleanLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
	}

	@Override
	public Node visit(NullLiteralExpr _n, Object _arg) {
		return new NullLiteralExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
	}

	@Override
	public Node visit(MethodCallExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);

		return new MethodCallExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, typeArgs, _n.getName(), args
		);
	}

	@Override
	public Node visit(NameExpr _n, Object _arg) {
		return new NameExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName()
		);
	}

	@Override
	public Node visit(ObjectCreationExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		ClassOrInterfaceType type_ = cloneNodes(_n.getType(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> anonymousBody = visit(_n.getAnonymousClassBody(), _arg);
		return new ObjectCreationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, type_, typeArgs, args, anonymousBody
		);
	}

	@Override
	public Node visit(QualifiedNameExpr _n, Object _arg) {
		NameExpr scope = cloneNodes(_n.getQualifier(), _arg);

		return new QualifiedNameExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, _n.getName()
		);
	}

	@Override
	public Node visit(ThisExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);

		return new ThisExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				classExpr
		);
	}

	@Override
	public Node visit(SuperExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);

		return new SuperExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				classExpr
		);
	}

	@Override
	public Node visit(UnaryExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		return new UnaryExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, _n.getOperator()
		);
	}

	@Override
	public Node visit(VariableDeclarationExpr _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> vars = visit(_n.getVars(), _arg);

		return new VariableDeclarationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, type_, vars
		);
	}

	@Override
	public Node visit(MarkerAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);

		return new MarkerAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name
		);
	}

	@Override
	public Node visit(SingleMemberAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Expression memberValue = cloneNodes(_n.getMemberValue(), _arg);

		return new SingleMemberAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, memberValue
		);
	}

	@Override
	public Node visit(NormalAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		List<MemberValuePair> pairs = visit(_n.getPairs(), _arg);

		return new NormalAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, pairs
		);
	}

	@Override
	public Node visit(MemberValuePair _n, Object _arg) {
		Expression value = cloneNodes(_n.getValue(), _arg);

		return new MemberValuePair(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), value
		);
	}

	@Override
	public Node visit(ExplicitConstructorInvocationStmt _n, Object _arg) {
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);

		return new ExplicitConstructorInvocationStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				typeArgs, _n.isThis(), expr, args
		);
	}

	@Override
	public Node visit(TypeDeclarationStmt _n, Object _arg) {
		TypeDeclaration typeDecl = cloneNodes(_n.getTypeDeclaration(), _arg);

		return new TypeDeclarationStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				typeDecl
		);
	}

	@Override
	public Node visit(AssertStmt _n, Object _arg) {
		Expression check = cloneNodes(_n.getCheck(), _arg);
		Expression message = cloneNodes(_n.getMessage(), _arg);

		return new AssertStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				check, message
		);
	}

	@Override
	public Node visit(BlockStmt _n, Object _arg) {
		List<Statement> stmts = visit(_n.getStmts(), _arg);

		return new BlockStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				stmts
		);
	}

	@Override
	public Node visit(LabeledStmt _n, Object _arg) {
		Statement stmt = cloneNodes(_n.getStmt(), _arg);

		return new LabeledStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getLabel(), stmt
		);
	}

	@Override
	public Node visit(EmptyStmt _n, Object _arg) {
		return new EmptyStmt(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
	}

	@Override
	public Node visit(ExpressionStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpression(), _arg);

		return new ExpressionStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr
		);
	}

	@Override
	public Node visit(SwitchStmt _n, Object _arg) {
		Expression selector = cloneNodes(_n.getSelector(), _arg);
		List<SwitchEntryStmt> entries = visit(_n.getEntries(), _arg);

		return new SwitchStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				selector, entries
		);
	}

	@Override
	public Node visit(SwitchEntryStmt _n, Object _arg) {
		Expression label = cloneNodes(_n.getLabel(), _arg);
		List<Statement> stmts = visit(_n.getStmts(), _arg);

		return new SwitchEntryStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				label, stmts
		);
	}

	@Override
	public Node visit(BreakStmt _n, Object _arg) {
		return new BreakStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getId()
		);
	}

	@Override
	public Node visit(ReturnStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		return new ReturnStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr
		);
	}

	@Override
	public Node visit(IfStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement thenStmt = cloneNodes(_n.getThenStmt(), _arg);
		Statement elseStmt = cloneNodes(_n.getElseStmt(), _arg);

		return new IfStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, thenStmt, elseStmt
		);
	}

	@Override
	public Node visit(WhileStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		return new WhileStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, body
		);
	}

	@Override
	public Node visit(ContinueStmt _n, Object _arg) {
		return new ContinueStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getId()
		);
	}

	@Override
	public Node visit(DoStmt _n, Object _arg) {
		Statement body = cloneNodes(_n.getBody(), _arg);
		Expression condition = cloneNodes(_n.getCondition(), _arg);

		return new DoStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				body, condition
		);
	}

	@Override
	public Node visit(ForeachStmt _n, Object _arg) {
		VariableDeclarationExpr var = cloneNodes(_n.getVariable(), _arg);
		Expression iterable = cloneNodes(_n.getIterable(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		return new ForeachStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				var, iterable, body
		);
	}

	@Override
	public Node visit(ForStmt _n, Object _arg) {
		List<Expression> init = visit(_n.getInit(), _arg);
		Expression compare = cloneNodes(_n.getCompare(), _arg);
		List<Expression> update = visit(_n.getUpdate(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);

		return new ForStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				init, compare, update, body
		);
	}

	@Override
	public Node visit(ThrowStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);

		return new ThrowStmt(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(), expr);
	}

	@Override
	public Node visit(SynchronizedStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);

		return new SynchronizedStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, block
		);
	}

	@Override
	public Node visit(TryStmt _n, Object _arg) {
		BlockStmt tryBlock = cloneNodes(_n.getTryBlock(), _arg);
		List<CatchClause> catchs = visit(_n.getCatchs(), _arg);
		BlockStmt finallyBlock = cloneNodes(_n.getFinallyBlock(), _arg);

		return new TryStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				tryBlock, catchs, finallyBlock
		);
	}

	@Override
	public Node visit(CatchClause _n, Object _arg) {
		Parameter except = cloneNodes(_n.getExcept(), _arg);
		BlockStmt catchBlock = cloneNodes(_n.getCatchBlock(), _arg);

		return new CatchClause(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				except, catchBlock
		);
	}

	public <T extends Node> List<T> visit(List<T> _nodes, Object _arg) {
		if (_nodes == null)
			return null;
		List<T> r = new ArrayList<T>(_nodes.size());
		for (T n : _nodes) {
			T rN = cloneNodes(n, _arg);
			if (rN != null)
				r.add(rN);
		}
		return r;
	}

	protected <T extends Node> T cloneNodes(T _node, Object _arg) {
		if (_node == null)
			return null;
		Node r = _node.accept(this, _arg);
		if (r == null)
			return null;
		return (T) r;
	}
}
