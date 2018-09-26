#include <cstdio>
#include <cstdlib>
#include <string>
#include <map>
#include <vector>
#include <iostream> 
using namespace std;  


//===----------------------------------------------------------------------===//
// VSL Lexer
//===----------------------------------------------------------------------===//

enum Token {
  tok_eof = -1,

  // commands
  tok_FUNC = -2,tok_VAR = -3,tok_IF = -4,tok_ELSE = -5,tok_THEN = -6,tok_FI = -7,tok_WHILE = -8,tok_DO = -9,tok_DONE = -10,tok_RETURN = -11,tok_PRINT = -12,tok_ASSIGN = -13,
  tok_CONTINUE=-14,tok_main=-15,
  // primary
  tok_var = -16 ,tok_number = -17 ,tok_text = -18 ,tok_P=-19,tok_err=-20//不是关键字的常量（这个现阶段没啥用），以后可以用来定义常量或者直接不能定义常量而报错 
};

static std::string IdentifierStr;  
static double NumVal;
static std::string TEXT;              

/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = getchar();

  if (isupper(LastChar)) { 
    IdentifierStr = LastChar;
    while (isupper((LastChar = getchar())))
      IdentifierStr += LastChar;
    if (IdentifierStr == "FUNC") return tok_FUNC;
    if (IdentifierStr == "VAR") return tok_VAR;
    if (IdentifierStr == "IF") return tok_IF;
    if (IdentifierStr == "ELSE") return tok_ELSE;
    if (IdentifierStr == "THEN") return tok_THEN;
    if (IdentifierStr == "FI") return tok_FI;
    if (IdentifierStr == "WHILE") return tok_WHILE;
    if (IdentifierStr == "DO") return tok_DO;
    if (IdentifierStr == "DONE") return tok_DONE;
    if (IdentifierStr == "RETURN") return tok_RETURN;
    if (IdentifierStr == "PRINT") return tok_PRINT;
    if (IdentifierStr == "CONTINUE") return tok_CONTINUE;
    return tok_P;
  }
  if(islower(LastChar)){
      IdentifierStr = LastChar;
  	 while(islower(LastChar = getchar())||isdigit(LastChar)){
      IdentifierStr += LastChar;
	   }
	   if(IdentifierStr=="main"){
	   	return tok_main;
	   }
      return tok_var;
  }
  if (isdigit(LastChar)) {   // Number: [0-9]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar));
    NumVal = strtod(NumStr.c_str(), 0);
    return tok_number;
  }
  if(LastChar == '"'){
  	TEXT = LastChar;
    while ((LastChar = getchar())!='"'||(LastChar = getchar())!='\n')
      TEXT += LastChar;
      if(LastChar=='"'){
      LastChar=getchar();
      return tok_text;
	  }
	  return tok_err;
  }
  if(LastChar == ':'){
    if((LastChar = getchar())=='='){
      LastChar=getchar();
      return tok_ASSIGN;
	}
  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
  }

  if (LastChar == '/') {
    // Comment until end of line.
    do LastChar = getchar();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF)
      return gettok();
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
}

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() {}
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;
public:
  NumberExprAST(double val) : Val(val) {}
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;
public:
  VariableExprAST(const std::string &name) : Name(name) {}
};
/// StarementsExprAST - Expression class for referencing a many of statement.
class StarementsExprAST : public ExprAST {
  std::vector<ExprAST*> Statements;
public:
  StarementsExprAST(std::vector<ExprAST*> &statements) 
  	: Statements(statements) {}
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  ExprAST *LHS, *RHS;
public:
  BinaryExprAST(char op, ExprAST *lhs, ExprAST *rhs)
    : Op(op), LHS(lhs), RHS(rhs) {}
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<ExprAST*> Args;
public:
  CallExprAST(const std::string &callee, std::vector<ExprAST*> &args)
    : Callee(callee), Args(args) {}
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
public:
  PrototypeAST(const std::string &name, const std::vector<std::string> &args)
    : Name(name), Args(args) {}

};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  PrototypeAST *Proto;
  ExprAST *Body;
public:
  FunctionAST(PrototypeAST *proto, ExprAST *body)
    : Proto(proto), Body(body) {}

};

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() {
  return CurTok = gettok();
}

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0) return -1;
  return TokPrec;
}

/// Error* - These are little helper functions for error handling.
ExprAST *Error(const char *Str) { fprintf(stderr, "Error: %s\n", Str);return 0;}
PrototypeAST *ErrorP(const char *Str) { Error(Str); return 0; }
FunctionAST *ErrorF(const char *Str) { Error(Str); return 0; }

static ExprAST *ParseExpression();
static ExprAST *ParseStatement();

static ExprAST *ParseVARExpr() {
  getNextToken();  // eat tok_VAR.
	  std::string IdName = IdentifierStr;
  getNextToken();  // eat identifierStr.
  return new VariableExprAST(IdName);
}
/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static ExprAST *ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;

  getNextToken();  // eat identifier.

  if (CurTok != '(') // Simple variable ref.
    return new VariableExprAST(IdName);

  // Call.
  getNextToken();  // eat (
  std::vector<ExprAST*> Args;
  if (CurTok != ')') {
    while (1) {
      ExprAST *Arg = ParseExpression();
      if (!Arg) return 0;
      Args.push_back(Arg);

      if (CurTok == ')') break;

      if (CurTok != ',')
        return Error("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }

  // Eat the ')'.
  getNextToken();

  return new CallExprAST(IdName, Args);
}

/// numberexpr ::= number
static ExprAST *ParseNumberExpr() {
  ExprAST *Result = new NumberExprAST(NumVal);
  getNextToken(); // consume the number
  return Result;
}

/// parenexpr ::= '(' expression ')'
static ExprAST *ParseParenExpr() {
  getNextToken();  // eat (.
  ExprAST *V = ParseExpression();
  if (!V) return 0;

  if (CurTok != ')')
    return Error("expected ')'");
  getNextToken();  // eat ).
  return V;
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static ExprAST *ParsePrimary() {
  switch (CurTok) {
  default: return Error("unknown token when expecting an expression");
  case tok_VAR: return ParseIdentifierExpr();
  case tok_number:     return ParseNumberExpr();
  case '(':            return ParseParenExpr();
  }
}

/// binoprhs
///   ::= ('+' primary)*
static ExprAST *ParseBinOpRHS(int ExprPrec, ExprAST *LHS) {
  // If this is a binop, find its precedence.
  while (1) {
    int TokPrec = GetTokPrecedence();

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec)
      return LHS;

    // Okay, we know this is a binop.
    int BinOp = CurTok;
    getNextToken();  // eat binop

    // Parse the primary expression after the binary operator.
    ExprAST *RHS = ParsePrimary();
    if (!RHS) return 0;

    // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec+1, RHS);
      if (RHS == 0) return 0;
    }

    // Merge LHS/RHS.
    LHS = new BinaryExprAST(BinOp, LHS, RHS);
  }
}

/// expression
///   ::= primary binoprhs
///
static ExprAST *ParseExpression() {
	
  ExprAST *LHS = ParsePrimary();
  if (!LHS) return 0;
  return ParseBinOpRHS(0, LHS);
}

static ExprAST *ParseBlock() {
	std::vector<ExprAST*> statements;
  if (CurTok != '{')
    return Error("Expected '{' in Expression");
  getNextToken(); 
  while (CurTok==tok_VAR) {
  statements.push_back(ParseVARExpr());
  };
  
  while (CurTok==tok_var||CurTok==tok_RETURN||CurTok==tok_PRINT||CurTok==tok_CONTINUE||CurTok==tok_IF||CurTok==tok_WHILE||CurTok=='{') {
  statements.push_back(ParseStatement());
  };
  if (CurTok != '}')
    return Error("Expected '}' in Expression");
	return new StarementsExprAST(statements);
}

static ExprAST *ParseStatement() {
	std::vector<ExprAST*> statements;
	 switch (CurTok) {
  default: return Error("unknown token when expecting an expression");
  case tok_var:  statements.push_back(ParseNumberExpr());
  case tok_RETURN:  statements.push_back(ParseNumberExpr());
  case tok_PRINT:     statements.push_back(ParseNumberExpr());
  case tok_CONTINUE:  statements.push_back(ParseNumberExpr());
  case tok_IF:     statements.push_back(ParseNumberExpr());
  case tok_WHILE:     statements.push_back(ParseNumberExpr());
  case '{':            statements.push_back(ParseBlock());
  }
  return new StarementsExprAST(statements);
}

/// prototype
///   ::= id '(' id* ')'
static PrototypeAST *ParsePrototype() {
  if (CurTok != tok_var&&CurTok != tok_main)
    return ErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  if(CurTok==tok_main){
  	fprintf(stderr, "Main:");
  }
  getNextToken();
  if (CurTok != '('){
    return ErrorP("Expected '(' in prototype");
  }

  std::vector<std::string> ArgNames;
  getNextToken();
  while ( CurTok== tok_var){
    ArgNames.push_back(IdentifierStr);
    if(getNextToken()==','){
    	if(getNextToken()==tok_var){
    	continue;
		}
		else{
			return ErrorP("Expected 'var' in prototype");
		}
	}
	else{
		break;
	}
  }
    
  if (CurTok != ')')
    return ErrorP("Expected ')' in prototype");

  // success.
  getNextToken();  // eat ')'.

  return new PrototypeAST(FnName, ArgNames);
}

static FunctionAST *ParseFUNC() {
  getNextToken();  // eat FUNC.
  PrototypeAST *Proto = ParsePrototype();
  if (Proto == 0) return 0;

  if (ExprAST *E = ParseStatement())
    return new FunctionAST(Proto, E);
  return 0;
}


static void HandleFUNC() {
  if (ParseFUNC()) {
    fprintf(stderr, "Parsed a FUNC\n");
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}


static void MainLoop() {
  while (1) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:    return;
    case tok_FUNC:    HandleFUNC(); break;
    default:         getNextToken(); break;
    }
  }
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;  // highest.

  // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextToken();

  // Run the main "interpreter loop" now.
  MainLoop();

  return 0;
}
