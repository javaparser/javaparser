package japa.parser.ast.visitor;

import java.util.ArrayList;
import java.util.List;

import japa.parser.ast.comments.BlockComment;
import japa.parser.ast.comments.Comment;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.ImportDeclaration;
import japa.parser.ast.comments.LineComment;
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
import japa.parser.ast.comments.JavadocComment;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.MultiTypeParameter;
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

		return new CompilationUnit(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				package_, imports, types
		);
	}

	@Override
	public Node visit(PackageDeclaration _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		PackageDeclaration r = new PackageDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				annotations, name
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ImportDeclaration _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ImportDeclaration r = new ImportDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, _n.isStatic(), _n.isAsterisk()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TypeParameter _n, Object _arg) {
		List<ClassOrInterfaceType> typeBound = visit(_n.getTypeBound(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		TypeParameter r = new TypeParameter(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), typeBound
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LineComment _n, Object _arg) {
		return new LineComment(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(), _n.getContent());
	}

	@Override
	public Node visit(BlockComment _n, Object _arg) {
		return new BlockComment(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(), _n.getContent());
	}

	@Override
	public Node visit(ClassOrInterfaceDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<ClassOrInterfaceType> extendsList = visit(_n.getExtends(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassOrInterfaceDeclaration r = new ClassOrInterfaceDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, _n.isInterface(), _n.getName(), typeParameters, extendsList, implementsList, members
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnumDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<ClassOrInterfaceType> implementsList = visit(_n.getImplements(), _arg);
		List<EnumConstantDeclaration> entries = visit(_n.getEntries(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnumDeclaration r = new EnumDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, _n.getName(), implementsList, entries, members
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyTypeDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyTypeDeclaration r = new EmptyTypeDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnumConstantDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> classBody = visit(_n.getClassBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnumConstantDeclaration r = new EnumConstantDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 annotations, _n.getName(), args, classBody
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AnnotationDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<BodyDeclaration> members = visit(_n.getMembers(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AnnotationDeclaration r = new AnnotationDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, _n.getName(), members
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AnnotationMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression defaultValue = cloneNodes(_n.getDefaultValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AnnotationMemberDeclaration r = new AnnotationMemberDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, type_, _n.getName(), defaultValue
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(FieldDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> variables = visit(_n.getVariables(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		FieldDeclaration r = new FieldDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, type_, variables
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclarator _n, Object _arg) {
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Expression init = cloneNodes(_n.getInit(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclarator r = new VariableDeclarator(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				id, init
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclaratorId _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclaratorId r = new VariableDeclaratorId(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), _n.getArrayCount()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ConstructorDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<TypeParameter> typeParameters = visit(_n.getTypeParameters(), _arg);
		List<Parameter> parameters = visit(_n.getParameters(), _arg);
		List<NameExpr> throws_ = visit(_n.getThrows(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ConstructorDeclaration r = new ConstructorDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, typeParameters, _n.getName(), parameters, throws_, block
		);
		r.setComment(comment);
		return r;
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
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MethodDeclaration r = new MethodDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.getModifiers(), annotations, typeParameters, type_, _n.getName(), parameters, _n.getArrayCount(), throws_, block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(Parameter _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		Parameter r = new Parameter(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, type_, _n.isVarArgs(), id
		);
		r.setComment(comment);
		return r;
	}
	
	@Override
	public Node visit(MultiTypeParameter _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		List<Type> types = visit(_n.getTypes(), _arg);
		VariableDeclaratorId id = cloneNodes(_n.getId(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MultiTypeParameter r = new MultiTypeParameter(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, types, id
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyMemberDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyMemberDeclaration r = new EmptyMemberDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(InitializerDeclaration _n, Object _arg) {
		JavadocComment javaDoc = cloneNodes(_n.getJavaDoc(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		InitializerDeclaration r = new InitializerDeclaration(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				 _n.isStatic(), block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(JavadocComment _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);
		JavadocComment r = new JavadocComment(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getContent()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ClassOrInterfaceType _n, Object _arg) {
		ClassOrInterfaceType scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassOrInterfaceType r = new ClassOrInterfaceType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, _n.getName(), typeArgs
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(PrimitiveType _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		PrimitiveType r = new PrimitiveType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getType()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ReferenceType _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ReferenceType r = new ReferenceType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, _n.getArrayCount()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VoidType _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VoidType r = new VoidType(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(WildcardType _n, Object _arg) {
		ReferenceType ext = cloneNodes(_n.getExtends(), _arg);
		ReferenceType sup = cloneNodes(_n.getSuper(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		WildcardType r = new WildcardType(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				ext, sup
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ArrayAccessExpr _n, Object _arg) {
		Expression name = cloneNodes(_n.getName(), _arg);
		Expression index = cloneNodes(_n.getIndex(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ArrayAccessExpr r = new ArrayAccessExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, index
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ArrayCreationExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<Expression> dimensions = visit(_n.getDimensions(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ArrayCreationExpr r = new ArrayCreationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, dimensions, _n.getArrayCount()
		);
		r.setComment(comment);
		if (_n.getInitializer() != null) // ArrayCreationExpr has two mutually exclusive constructors
			r.setInitializer(cloneNodes(_n.getInitializer(), _arg));
		return r;
	}

	@Override
	public Node visit(ArrayInitializerExpr _n, Object _arg) {
		List<Expression> values = visit(_n.getValues(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ArrayInitializerExpr r = new ArrayInitializerExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				values
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AssignExpr _n, Object _arg) {
		Expression target = cloneNodes(_n.getTarget(), _arg);
		Expression value = cloneNodes(_n.getValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AssignExpr r = new AssignExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				target, value, _n.getOperator());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BinaryExpr _n, Object _arg) {
		Expression left = cloneNodes(_n.getLeft(), _arg);
		Expression right = cloneNodes(_n.getRight(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BinaryExpr r = new BinaryExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				left, right, _n.getOperator()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CastExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CastExpr r = new CastExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_, expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ClassExpr _n, Object _arg) {
		Type type_ = cloneNodes(_n.getType(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ClassExpr r = new ClassExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				type_
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ConditionalExpr _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Expression thenExpr = cloneNodes(_n.getThenExpr(), _arg);
		Expression elseExpr = cloneNodes(_n.getElseExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ConditionalExpr r = new ConditionalExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, thenExpr, elseExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EnclosedExpr _n, Object _arg) {
		Expression inner = cloneNodes(_n.getInner(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EnclosedExpr r = new EnclosedExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				inner
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(FieldAccessExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		FieldAccessExpr r = new FieldAccessExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, typeArgs, _n.getField()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(InstanceOfExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		InstanceOfExpr r = new InstanceOfExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, type_
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(StringLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);
		StringLiteralExpr r = new StringLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IntegerLiteralExpr r = new IntegerLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LongLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LongLiteralExpr r = new LongLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IntegerLiteralMinValueExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IntegerLiteralMinValueExpr r = new IntegerLiteralMinValueExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LongLiteralMinValueExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LongLiteralMinValueExpr r = new LongLiteralMinValueExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CharLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CharLiteralExpr r = new CharLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(DoubleLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		DoubleLiteralExpr r = new DoubleLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BooleanLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BooleanLiteralExpr r = new BooleanLiteralExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getValue()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NullLiteralExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NullLiteralExpr r = new NullLiteralExpr(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MethodCallExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MethodCallExpr r = new MethodCallExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, typeArgs, _n.getName(), args
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NameExpr _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NameExpr r = new NameExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ObjectCreationExpr _n, Object _arg) {
		Expression scope = cloneNodes(_n.getScope(), _arg);
		ClassOrInterfaceType type_ = cloneNodes(_n.getType(), _arg);
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		List<BodyDeclaration> anonymousBody = visit(_n.getAnonymousClassBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ObjectCreationExpr r = new ObjectCreationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, type_, typeArgs, args, anonymousBody
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(QualifiedNameExpr _n, Object _arg) {
		NameExpr scope = cloneNodes(_n.getQualifier(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		QualifiedNameExpr r = new QualifiedNameExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				scope, _n.getName()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ThisExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ThisExpr r = new ThisExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				classExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SuperExpr _n, Object _arg) {
		Expression classExpr = cloneNodes(_n.getClassExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SuperExpr r = new SuperExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				classExpr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(UnaryExpr _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		UnaryExpr r = new UnaryExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, _n.getOperator()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(VariableDeclarationExpr _n, Object _arg) {
		List<AnnotationExpr> annotations = visit(_n.getAnnotations(), _arg);
		Type type_ = cloneNodes(_n.getType(), _arg);
		List<VariableDeclarator> vars = visit(_n.getVars(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		VariableDeclarationExpr r = new VariableDeclarationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getModifiers(), annotations, type_, vars
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MarkerAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MarkerAnnotationExpr r = new MarkerAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SingleMemberAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		Expression memberValue = cloneNodes(_n.getMemberValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SingleMemberAnnotationExpr r = new SingleMemberAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, memberValue
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(NormalAnnotationExpr _n, Object _arg) {
		NameExpr name = cloneNodes(_n.getName(), _arg);
		List<MemberValuePair> pairs = visit(_n.getPairs(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		NormalAnnotationExpr r = new NormalAnnotationExpr(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				name, pairs
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(MemberValuePair _n, Object _arg) {
		Expression value = cloneNodes(_n.getValue(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		MemberValuePair r = new MemberValuePair(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getName(), value
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ExplicitConstructorInvocationStmt _n, Object _arg) {
		List<Type> typeArgs = visit(_n.getTypeArgs(), _arg);
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		List<Expression> args = visit(_n.getArgs(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ExplicitConstructorInvocationStmt r = new ExplicitConstructorInvocationStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				typeArgs, _n.isThis(), expr, args
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TypeDeclarationStmt _n, Object _arg) {
		TypeDeclaration typeDecl = cloneNodes(_n.getTypeDeclaration(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		TypeDeclarationStmt r = new TypeDeclarationStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				typeDecl
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(AssertStmt _n, Object _arg) {
		Expression check = cloneNodes(_n.getCheck(), _arg);
		Expression message = cloneNodes(_n.getMessage(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		AssertStmt r = new AssertStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				check, message
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BlockStmt _n, Object _arg) {
		List<Statement> stmts = visit(_n.getStmts(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BlockStmt r = new BlockStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				stmts
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(LabeledStmt _n, Object _arg) {
		Statement stmt = cloneNodes(_n.getStmt(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		LabeledStmt r = new LabeledStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getLabel(), stmt
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(EmptyStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		EmptyStmt r = new EmptyStmt(_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn());
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ExpressionStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpression(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ExpressionStmt r = new ExpressionStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SwitchStmt _n, Object _arg) {
		Expression selector = cloneNodes(_n.getSelector(), _arg);
		List<SwitchEntryStmt> entries = visit(_n.getEntries(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SwitchStmt r = new SwitchStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				selector, entries
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SwitchEntryStmt _n, Object _arg) {
		Expression label = cloneNodes(_n.getLabel(), _arg);
		List<Statement> stmts = visit(_n.getStmts(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SwitchEntryStmt r = new SwitchEntryStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				label, stmts
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(BreakStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		BreakStmt r = new BreakStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getId()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ReturnStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ReturnStmt r = new ReturnStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(IfStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement thenStmt = cloneNodes(_n.getThenStmt(), _arg);
		Statement elseStmt = cloneNodes(_n.getElseStmt(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		IfStmt r = new IfStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, thenStmt, elseStmt
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(WhileStmt _n, Object _arg) {
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		WhileStmt r = new WhileStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				condition, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ContinueStmt _n, Object _arg) {
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ContinueStmt r = new ContinueStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				_n.getId()
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(DoStmt _n, Object _arg) {
		Statement body = cloneNodes(_n.getBody(), _arg);
		Expression condition = cloneNodes(_n.getCondition(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		DoStmt r = new DoStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				body, condition
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ForeachStmt _n, Object _arg) {
		VariableDeclarationExpr var = cloneNodes(_n.getVariable(), _arg);
		Expression iterable = cloneNodes(_n.getIterable(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ForeachStmt r = new ForeachStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				var, iterable, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ForStmt _n, Object _arg) {
		List<Expression> init = visit(_n.getInit(), _arg);
		Expression compare = cloneNodes(_n.getCompare(), _arg);
		List<Expression> update = visit(_n.getUpdate(), _arg);
		Statement body = cloneNodes(_n.getBody(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ForStmt r = new ForStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				init, compare, update, body
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(ThrowStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		ThrowStmt r = new ThrowStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(SynchronizedStmt _n, Object _arg) {
		Expression expr = cloneNodes(_n.getExpr(), _arg);
		BlockStmt block = cloneNodes(_n.getBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		SynchronizedStmt r = new SynchronizedStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				expr, block
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(TryStmt _n, Object _arg) {
		List<VariableDeclarationExpr> resources = visit(_n.getResources(),_arg);
		BlockStmt tryBlock = cloneNodes(_n.getTryBlock(), _arg);
		List<CatchClause> catchs = visit(_n.getCatchs(), _arg);
		BlockStmt finallyBlock = cloneNodes(_n.getFinallyBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		TryStmt r = new TryStmt(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				resources, tryBlock, catchs, finallyBlock
		);
		r.setComment(comment);
		return r;
	}

	@Override
	public Node visit(CatchClause _n, Object _arg) {
		MultiTypeParameter except = cloneNodes(_n.getExcept(), _arg);
		BlockStmt catchBlock = cloneNodes(_n.getCatchBlock(), _arg);
		Comment comment = cloneNodes(_n.getComment(), _arg);

		CatchClause r = new CatchClause(
				_n.getBeginLine(), _n.getBeginColumn(), _n.getEndLine(), _n.getEndColumn(),
				except.getModifiers(), except.getAnnotations(), except.getTypes(), except.getId(), catchBlock
		);
		r.setComment(comment);
		return r;
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
