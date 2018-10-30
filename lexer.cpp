#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>
using namespace llvm;
using namespace llvm::orc;

//===----------------------------------------------------------------------===//
// VSL Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,

  // commands
  tok_FUNC = -2,
  tok_VAR = -3,
  tok_IF = -4,
  tok_ELSE = -5,
  tok_THEN = -6,
  tok_FI = -7,
  tok_WHILE = -8,
  tok_DO = -9,
  tok_DONE = -10,
  tok_RETURN = -11,
  tok_PRINT = -12,
  tok_ASSIGN = -13,
  tok_CONTINUE = -14,
  tok_main = -15,
  // primary
  tok_var = -16,
  tok_number = -17,
  tok_text = -18,
  tok_P = -19,
  tok_err =
      -20 //涓嶆槸鍏抽敭瀛楃殑甯搁噺锛堣繖涓幇闃舵娌″暐鐢級锛屼互鍚庡彲浠ョ敤鏉ュ畾涔夊父閲忔垨鑰呯洿鎺ヤ笉鑳藉畾涔夊父閲忚€屾姤閿?
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
    if (IdentifierStr == "FUNC")
      return tok_FUNC;
    if (IdentifierStr == "VAR")
      return tok_VAR;
    if (IdentifierStr == "IF")
      return tok_IF;
    if (IdentifierStr == "ELSE")
      return tok_ELSE;
    if (IdentifierStr == "THEN")
      return tok_THEN;
    if (IdentifierStr == "FI")
      return tok_FI;
    if (IdentifierStr == "WHILE")
      return tok_WHILE;
    if (IdentifierStr == "DO")
      return tok_DO;
    if (IdentifierStr == "DONE")
      return tok_DONE;
    if (IdentifierStr == "RETURN")
      return tok_RETURN;
    if (IdentifierStr == "PRINT")
      return tok_PRINT;
    if (IdentifierStr == "CONTINUE")
      return tok_CONTINUE;
    return tok_P;
  }
  if (islower(LastChar)) {
    IdentifierStr = LastChar;
    while (islower(LastChar = getchar()) || isdigit(LastChar)) {
      IdentifierStr += LastChar;
    }
    if (IdentifierStr == "main") {
      return tok_main;
    }
    return tok_var;
  }
  if (isdigit(LastChar)) { // Number: [0-9]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar));
    NumVal = strtod(NumStr.c_str(), 0);
    return tok_number;
  }
  if (LastChar == '"') {
    TEXT = "";
    while ((LastChar = getchar()) != '"' && LastChar != '\n')
      TEXT += LastChar;
    if (LastChar == '"') {
      LastChar = getchar();
      return tok_text;
    }
    return tok_err;
  }
  if (LastChar == ':') {
    int ThisChar = LastChar;
    if ((LastChar = getchar()) == '=') {
      LastChar = getchar();
      return tok_ASSIGN;
    }
    return ThisChar;
  }

  if (LastChar == '/') {
    int ThisChar = LastChar;
    if ((LastChar = getchar())!= '/') {
      return ThisChar;
    }
    // Comment until end of line.
    do
      LastChar = getchar();
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

namespace {

/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() = default;

  virtual Value *codegen() = 0;
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double Val) : Val(Val) {}

  Value *codegen() override;
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(const std::string &Name) : Name(Name) {}

  Value *codegen() override;
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

  Value *codegen() override;
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}

  Value *codegen() override;
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;

public:
  PrototypeAST(const std::string &Name, std::vector<std::string> Args)
      : Name(Name), Args(std::move(Args)) {}

  Function *codegen();
  const std::string &getName() const { return Name; }
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}

  Function *codegen();
};

/// StarementsExprAST - Expression class for referencing a many of statement.
class StarementsExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> Statements;

public:
  StarementsExprAST(std::vector<std::unique_ptr<ExprAST>> statements)
      : Statements(std::move(statements)) {}
  Value *codegen() override;
};
/// StarementsExprAST - Expression class for referencing a many of statement.
class AssignmentExprAST : public ExprAST {
  std::string Name;
  std::unique_ptr<ExprAST> Expr;

public:
  AssignmentExprAST(const std::string &name, std::unique_ptr<ExprAST> expr)
      : Name(name), Expr(std::move(expr)) {}
  Value *codegen() override;
};
/// IFExprAST - Expression class for if statement.
class IFExprAST : public ExprAST {
  std::unique_ptr<ExprAST> CondExpr;
  std::unique_ptr<ExprAST> THENExpr;
  std::unique_ptr<ExprAST> ELSEExpr;

public:
  IFExprAST(std::unique_ptr<ExprAST> condexpr,
            std::unique_ptr<ExprAST> thenexpr,
            std::unique_ptr<ExprAST> elseexpr)
      : CondExpr(std::move(condexpr)), THENExpr(std::move(thenexpr)),
        ELSEExpr(std::move(elseexpr)) {}
  Value *codegen() override;
};
/// WHILEExprAST - Expression class for  while statement.
class WHILEExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Expr;
  std::unique_ptr<ExprAST> DOExpr;

public:
  WHILEExprAST(std::unique_ptr<ExprAST> expr, std::unique_ptr<ExprAST> doexpr)
      : Expr(std::move(expr)), DOExpr(std::move(doexpr)) {}
  Value *codegen() override;
};

/// PRINTITEMExprAST - Expression class for  printitem statement.
class PRINTITEMExprAST : public ExprAST {
  std::string Text;
  std::unique_ptr<ExprAST> Expr;

public:
  PRINTITEMExprAST(const std::string &text, std::unique_ptr<ExprAST> expr)
      : Text(text), Expr(std::move(expr)) {}
  Value *codegen() override;
};

/// PRINTExprAST - Expression class for  printitem statement.
class PRINTExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> Items;

public:
  PRINTExprAST(std::vector<std::unique_ptr<ExprAST>> items)
      : Items(std::move(items)) {}
  Value *codegen() override;
};

/// RETURNExprAST - Expression class for  return statement.
class RETURNExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Expr;

public:
  RETURNExprAST(std::unique_ptr<ExprAST> expr) : Expr(std::move(expr)) {}
  Value *codegen() override;
};
/// NULLExprAST - Expression class for continue statement.
class NULLExprAST : public ExprAST {
public:
  NULLExprAST() {}
  Value *codegen() override;
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() { return CurTok = gettok(); }

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

/// LogLogError* - These are little helper functions for LogError handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
  fprintf(stderr, "LogError: %s\n", Str);
  return nullptr;
}

std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
  LogError(Str);
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();
static std::unique_ptr<ExprAST> ParseStatement();

static std::unique_ptr<ExprAST> ParseVARExpr() {
  getNextToken(); // eat tok_VAR.
  std::string IdName = IdentifierStr;
  getNextToken(); // eat identifierStr.
  return llvm::make_unique<VariableExprAST>(IdName);
}

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto Result = llvm::make_unique<NumberExprAST>(NumVal);
  getNextToken(); // consume the number
  return std::move(Result);
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); // eat (.
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken(); // eat ).
  return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;

  getNextToken(); // eat identifier.

  if (CurTok != '(') // Simple variable ref.
    return llvm::make_unique<VariableExprAST>(IdName);

  // Call.
  getNextToken(); // eat (
  std::vector<std::unique_ptr<ExprAST>> Args;
  if (CurTok != ')') {
    while (true) {
      if (auto Arg = ParseExpression())
        Args.push_back(std::move(Arg));
      else
        return nullptr;

      if (CurTok == ')')
        break;

      if (CurTok != ',')
        return LogError("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }

  // Eat the ')'.
  getNextToken();

  return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}

//取负处理器
static std::unique_ptr<ExprAST> ParseFuExpr() {
  auto Result = llvm::make_unique<NumberExprAST>(0);
  int FuTok= CurTok;
  getNextToken();
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseIdentifierExpr()));
  case tok_number:
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseNumberExpr()));
  case '(':
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseParenExpr()));
  }
 
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    return ParseIdentifierExpr();
  case tok_number:
    return ParseNumberExpr();
  case '(':
    return ParseParenExpr();
  case '-':
    return ParseFuExpr();
  }
}

/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
  // If this is a binop, find its precedence.
  while (true) {
    int TokPrec = GetTokPrecedence();

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec)
      return LHS;

    // Okay, we know this is a binop.
    int BinOp = CurTok;
    getNextToken(); // eat binop

    // Parse the primary expression after the binary operator.
    auto RHS = ParsePrimary();
    if (!RHS)
      return nullptr;

    // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
      if (!RHS)
        return nullptr;
    }

    // Merge LHS/RHS.
    LHS =
        llvm::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
  }
}

/// expression
///   ::= primary binoprhs
///
static std::unique_ptr<ExprAST> ParseExpression() {
  auto LHS = ParsePrimary();
  if (!LHS)
    return nullptr;

  return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAST> ParseAssignment() {

  if (CurTok != tok_var)
    return LogError("Expected variable in Expression");
  std::string IdName = IdentifierStr;
  getNextToken();
  if (CurTok != tok_ASSIGN)
    return LogError("Expected ':=' in Expression");
  getNextToken();
  if (CurTok != tok_number && CurTok != tok_var && CurTok != '-' &&
      CurTok != '(')
    return LogError("Expected an expression in Expression");
  return llvm::make_unique<AssignmentExprAST>(IdName,
                                              std::move(ParseExpression()));
}

static std::unique_ptr<ExprAST> ParseIF() {

  if (CurTok != tok_IF)
    return LogError("Expected IF in Expression");
  getNextToken();
  std::unique_ptr<ExprAST> ifexpr = ParseExpression();
  if (!ifexpr)
    return nullptr;
  if (CurTok != tok_THEN)
    return LogError("Expected THEN in Expression");
  getNextToken();
  std::unique_ptr<ExprAST> thenexpr = ParseExpression();
  if (!thenexpr)
    return nullptr;
  // getNextToken();
  std::unique_ptr<ExprAST> elseexpr;
  if (CurTok == tok_ELSE) {
    getNextToken();
    elseexpr = ParseExpression();
    //    getNextToken();
  }
  if (!elseexpr)
    return nullptr;
  if (CurTok != tok_FI)
    return LogError("Expected FI in Expression");
  getNextToken();
  return llvm::make_unique<IFExprAST>(std::move(ifexpr), std::move(thenexpr),
                                      std::move(elseexpr));
}

static std::unique_ptr<ExprAST> ParseWHILE() {

  if (CurTok != tok_WHILE)
    return LogError("Expected WHILE in Expression");
  getNextToken();
  std::unique_ptr<ExprAST> whileexpr = ParseExpression();
  if (CurTok != tok_DO)
    return LogError("Expected DO in Expression");
  getNextToken();
  std::unique_ptr<ExprAST> doexpr = ParseExpression();
  //getNextToken();
  if (CurTok != tok_DONE)
    return LogError("Expected DONE in Expression");
  getNextToken();
  return llvm::make_unique<WHILEExprAST>(std::move(whileexpr),
                                         std::move(doexpr));
}
static std::unique_ptr<ExprAST> ParseCONTINUE() {

  if (CurTok != tok_CONTINUE)
    return LogError("Expected CONTINUE in Expression");
  getNextToken();
  return llvm::make_unique<NULLExprAST>();
}

static std::unique_ptr<ExprAST> ParseRETURN() {

  if (CurTok != tok_RETURN)
    return LogError("Expected RETURN in Expression");
  getNextToken();
  return llvm::make_unique<RETURNExprAST>(std::move(ParseExpression()));
}

static std::unique_ptr<ExprAST> ParsePRINTITEM() {

  if (CurTok != tok_text && CurTok != tok_number && CurTok != tok_var &&
      CurTok != '-' && CurTok != '(')
    return LogError("Expected epxr or string in Expression");
  std::unique_ptr<ExprAST> epxr;
  std::string text;
  if (CurTok == tok_text) {
    text = TEXT;
    getNextToken();
  } else {
    epxr = ParseExpression();
  }
  return llvm::make_unique<PRINTITEMExprAST>(text, std::move(epxr));
}

static std::unique_ptr<ExprAST> ParsePRINT() {
  std::vector<std::unique_ptr<ExprAST>> items;
  if (CurTok != tok_PRINT)
    return LogError("Expected PRINT in Expression");
  getNextToken();
  if (CurTok != tok_text && CurTok != tok_number && CurTok != tok_var &&
      CurTok != '-' && CurTok != '(')
    return LogError("Expected epxr or string in Expression");
  items.push_back(ParsePRINTITEM());
  while (CurTok == ',') {
    getNextToken();
    items.push_back(ParsePRINTITEM());
  }
  return llvm::make_unique<StarementsExprAST>(std::move(items));
}

static std::unique_ptr<ExprAST> ParseBlock() {
  std::vector<std::unique_ptr<ExprAST>> statements;
  if (CurTok != '{')
    return LogError("Expected '{' in Expression");
  getNextToken();
  while (CurTok == tok_VAR) {
    statements.push_back(ParseVARExpr());
  };

  while (CurTok == tok_var || CurTok == tok_RETURN || CurTok == tok_PRINT ||
         CurTok == tok_CONTINUE || CurTok == tok_IF || CurTok == tok_WHILE ||
         CurTok == '{') {
    statements.push_back(ParseStatement());
  };
  if (CurTok != '}')
    return LogError("Expected '}' in Expression");
  return llvm::make_unique<StarementsExprAST>(std::move(statements));
}

static std::unique_ptr<ExprAST> ParseStatement() {

  std::vector<std::unique_ptr<ExprAST>> statements;
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    statements.push_back(ParseAssignment());
    break;
  case tok_RETURN:
    statements.push_back(ParseRETURN());
    break;
  case tok_PRINT:
    statements.push_back(ParsePRINT());
    break;
  case tok_CONTINUE:
    statements.push_back(ParseCONTINUE());
    break;
  case tok_IF:
    statements.push_back(ParseIF());
    break;
  case tok_WHILE:
    statements.push_back(ParseWHILE());
    break;
  case '{':
    statements.push_back(ParseBlock());
    break;
  }

  return llvm::make_unique<StarementsExprAST>(std::move(statements));
}
/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_FUNC)
    return LogErrorP("Expected FUNC in prototype");
  getNextToken();
  if (CurTok != tok_var && CurTok != tok_main)
    return LogErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  if (CurTok == tok_main) {
    fprintf(stderr, "Main:");
  }
  getNextToken();
  if (CurTok != '(') {
    return LogErrorP("Expected '(' in prototype");
  }

  std::vector<std::string> ArgNames;
  getNextToken();
  while (CurTok == tok_var) {
    ArgNames.push_back(IdentifierStr);
    if (getNextToken() == ',') {
      if (getNextToken() == tok_var) {
        continue;
      } else {
        return LogErrorP("Expected 'var' in prototype");
      }
    } else {
      break;
    }
  }

  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  // success.
  getNextToken(); // eat ')'.

  return llvm::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseFUNC() {
  auto ProtoAST = ParsePrototype();
  if (!ProtoAST)
    return nullptr;
  if (auto E = ParseStatement()) {
    // Make an anonymous proto.
    return llvm::make_unique<FunctionAST>(std::move(ProtoAST), std::move(E));
  }
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;

static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

Value *LogErrorV(const char *Str) {
  LogError(Str);
  return nullptr;
}

Function *getFunction(std::string Name) {
  // First, see if the function has already been added to the current module.
  if (auto *F = TheModule->getFunction(Name))
    return F;

  // If not, check whether we can codegen the declaration from some existing
  // prototype.
  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end())
    return FI->second->codegen();

  // If no existing prototype exists, return null.
  return nullptr;
}

Value *NumberExprAST::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Unknown variable name");
  return V;
}

Value *BinaryExprAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  if (!L || !R)
    return nullptr;

  switch (Op) {
  case '+':
    return Builder.CreateFAdd(L, R, "addtmp");
  case '-':
    return Builder.CreateFSub(L, R, "subtmp");
  case '*':
    return Builder.CreateFMul(L, R, "multmp");
  case '/':
    return Builder.CreateFDiv(L, R, "divtmp");
  case '<':
    L = Builder.CreateFCmpULT(L, R, "cmptmp");
    // Convert bool 0/1 to double 0.0 or 1.0
    return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
  default:
    return LogErrorV("invalid binary operator");
  }
}

Value *CallExprAST::codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = getFunction(Callee);
  if (!CalleeF)
    return LogErrorV("Unknown function referenced");

  // If argument mismatch LogError.
  if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect # arguments passed");

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }

  return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Function *PrototypeAST::codegen() {
  // Make the function type:  double(double,double) etc.
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(TheContext));
  FunctionType *FT =
      FunctionType::get(Type::getDoubleTy(TheContext), Doubles, false);

  Function *F =
      Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  // Set names for all arguments.
  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Args[Idx++]);

  return F;
}

Function *FunctionAST::codegen() {
  // First, check for an existing function from a previous 'extern' declaration.
  auto &P = *Proto;
  FunctionProtos[Proto->getName()] = std::move(Proto);
  Function *TheFunction = getFunction(P.getName());

  if (!TheFunction)
    TheFunction = Proto->codegen();

  if (!TheFunction)
    return nullptr;

  // Create a new basic block to start insertion into.
  BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
  Builder.SetInsertPoint(BB);

  // Record the function arguments in the NamedValues map.
  NamedValues.clear();
  for (auto &Arg : TheFunction->args())
    NamedValues[Arg.getName()] = &Arg;

  if (Value *RetVal = Body->codegen()) {
    // Finish off the function.
    Builder.CreateRet(RetVal);

    // Validate the generated code, checking for consistency.
    verifyFunction(*TheFunction);

    // Run the optimizer on the function.
    TheFPM->run(*TheFunction);

    return TheFunction;
  }

  // LogError reading body, remove function.
  TheFunction->eraseFromParent();
  return nullptr;
}
Value *IFExprAST::codegen() {
  Value *CondV = CondExpr->codegen();
  if (!CondV)
    return nullptr;

  // Convert condition to a bool by comparing non-equal to 0.0.
  CondV = Builder.CreateFCmpONE(
      CondV, ConstantFP::get(TheContext, APFloat(0.0)), "ifcond");

  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  // Create blocks for the then and else cases.  Insert the 'then' block at the
  // end of the function.
  BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
  BasicBlock *ElseBB = BasicBlock::Create(TheContext, "else");
  BasicBlock *MergeBB = BasicBlock::Create(TheContext, "ifcont");

  Builder.CreateCondBr(CondV, ThenBB, ElseBB);

  // Emit then value.
  Builder.SetInsertPoint(ThenBB);

  Value *ThenV = THENExpr->codegen();
  if (!ThenV)
    return nullptr;

  Builder.CreateBr(MergeBB);
  // Codegen of 'Then' can change the current block, update ThenBB for the PHI.
  ThenBB = Builder.GetInsertBlock();

  // Emit else block.
  TheFunction->getBasicBlockList().push_back(ElseBB);
  Builder.SetInsertPoint(ElseBB);

  Value *ElseV = ELSEExpr->codegen();
  if (!ElseV)
    return nullptr;

  Builder.CreateBr(MergeBB);
  // Codegen of 'Else' can change the current block, update ElseBB for the PHI.
  ElseBB = Builder.GetInsertBlock();

  // Emit merge block.
  TheFunction->getBasicBlockList().push_back(MergeBB);
  Builder.SetInsertPoint(MergeBB);
  PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 2, "iftmp");

  PN->addIncoming(ThenV, ThenBB);
  PN->addIncoming(ElseV, ElseBB);
  return PN;
}
Value *AssignmentExprAST::codegen() { return nullptr; }
Value *StarementsExprAST::codegen() {
  int count = Statements.size();
  for (int i = 0; i < count; i++) {
    return Statements[i]->codegen();
  }
}
Value *WHILEExprAST::codegen() {

  // Make the new basic block for the loop header, inserting after current
  // block.
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop", TheFunction);

  // Insert an explicit fall through from the current block to the LoopBB.
  Builder.CreateBr(LoopBB);

  // Start insertion in LoopBB.
  Builder.SetInsertPoint(LoopBB);

  if (!DOExpr->codegen())
    return nullptr;
  // Compute the end condition.
  Value *EndCond = Expr->codegen();
  if (!EndCond)
    return nullptr;
  EndCond = Builder.CreateFCmpONE(
      EndCond, ConstantFP::get(TheContext, APFloat(0.0)), "loopcond");

  BasicBlock *AfterBB =
      BasicBlock::Create(TheContext, "afterloop", TheFunction);

  // Insert the conditional branch into the end of LoopEndBB.
  Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

  // Any new code will be inserted in AfterBB.
  Builder.SetInsertPoint(AfterBB);
  // for expr always returns 0.0.
  return Constant::getNullValue(Type::getDoubleTy(TheContext));
}
Value *PRINTITEMExprAST::codegen() { return nullptr; }

Value *PRINTExprAST::codegen() { return nullptr; }
Value *RETURNExprAST::codegen() { return nullptr; }
Value *NULLExprAST::codegen() { return nullptr; }

//=
//------------------------------------------------------------- ==
//   = //
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void InitializeModuleAndPassManager() {
  // Open a new module.
  TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
  TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());

  // Create a new pass manager attached to it.
  TheFPM = llvm::make_unique<legacy::FunctionPassManager>(TheModule.get());

  // Do simple "peephole" optimizations and bit-twiddling optzns.
  TheFPM->add(createInstructionCombiningPass());
  // Reassociate expressions.
  TheFPM->add(createReassociatePass());
  // Eliminate Common SubExpressions.
  TheFPM->add(createGVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  TheFPM->add(createCFGSimplificationPass());

  TheFPM->doInitialization();
}

static void HandleFUNC() {
  if (auto FnAST = ParseFUNC()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Parsed a FUNC\n");
      FnIR->print(errs());
      fprintf(stderr, "\n");
      TheJIT->addModule(std::move(TheModule));
      InitializeModuleAndPassManager();
    }
  } else {
    // Skip token for LogError recovery.
    getNextToken();
  }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
  while (1) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case tok_FUNC:
      HandleFUNC();
      break;
    default:
      getNextToken();
      break;
    }
  }
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['/'] = 40; 
  BinopPrecedence['*'] = 40; // highest.

  // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextToken();

  TheJIT = llvm::make_unique<KaleidoscopeJIT>();

  InitializeModuleAndPassManager();
  // Run the main "interpreter loop" now.
  MainLoop();

  return 0;
}
