#include "../include/KaleidoscopeJIT.h"
#include <iostream>
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
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Utils.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <queue>
#include <string>
#include <utility>
#include <vector>
using namespace llvm;
using namespace llvm::sys;

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
  tok_err = -20 //
};

static std::string IdentifierStr;
static double NumVal;
static std::string TEXT;
static std::vector<std::string> cifa;
static std::vector<std::string> yufa;
static std::string space="";

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
    if (IdentifierStr == "FUNC") {
      cifa.push_back("FUNC--tok_FUNC");
      return tok_FUNC;
    }
    if (IdentifierStr == "VAR") {
      cifa.push_back("VAR--tok_VAR");
      return tok_VAR;
	}
    if (IdentifierStr == "IF") {
          cifa.push_back("IF--tok_IF");
          return tok_IF;
	}
    if (IdentifierStr == "ELSE") {
          cifa.push_back("ELSE--tok_ELSE");
          return tok_ELSE;
	}
    if (IdentifierStr == "THEN") {
      cifa.push_back("THEN--tok_THEN");
          return tok_THEN;
	}
    if (IdentifierStr == "FI") {
      cifa.push_back("FI--tok_FI");
          return tok_FI;
	}
    if (IdentifierStr == "WHILE") {
          cifa.push_back("WHILE--tok_WHILE");
          return tok_WHILE;
	}
    if (IdentifierStr == "DO") {
          cifa.push_back("DO--tok_DO");
          return tok_DO;
	}
    if (IdentifierStr == "DONE") {
          cifa.push_back("DONE--tok_DONE");
          return tok_DONE;
	}
    if (IdentifierStr == "RETURN") {
          cifa.push_back("RETURN--tok_RETURN");
          return tok_RETURN;
	}
    if (IdentifierStr == "PRINT") {
          cifa.push_back("PRINT--tok_PRINT");
          return tok_PRINT;
	}
    if (IdentifierStr == "CONTINUE") {
          cifa.push_back("CONTINUE--tok_CONTINUE");
          return tok_CONTINUE;
	}
    return tok_P;
  }
  if (islower(LastChar)) {
    IdentifierStr = LastChar;
    while (islower(LastChar = getchar()) || isdigit(LastChar)) {
      IdentifierStr += LastChar;
    }
    if (IdentifierStr == "main") {
      cifa.push_back("main--tok_Variable");
      return tok_main;
    }
    cifa.push_back(IdentifierStr +"--tok_var");
    return tok_var;
  }
  if (isdigit(LastChar)) { // Number: [0-9]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar));
    cifa.push_back(NumStr + "--tok_number");
    NumVal = strtod(NumStr.c_str(), 0);
    return tok_number;
  }
  if (LastChar == '"') {
    TEXT = "";
    while ((LastChar = getchar()) != '"' && LastChar != '\n')
      TEXT += LastChar;
    if (LastChar == '"') {
      LastChar = getchar();
      cifa.push_back(TEXT + "--tok_text");
      return tok_text;
    }
    return tok_err;
  }
  if (LastChar == ':') {
    int ThisChar = LastChar;
    if ((LastChar = getchar()) == '=') {
      LastChar = getchar();
      cifa.push_back(":=--tok_ASSIGN");
      return tok_ASSIGN;
    }
    cifa.push_back(":--tok_Symbol");
    return ThisChar;
  }

  if (LastChar == '/') {
    int ThisChar = LastChar;
    if ((LastChar = getchar()) != '/') {
      cifa.push_back("/--tok_Symbol");
      return ThisChar;
    }
    // Comment until end of line.
    do
      LastChar = getchar();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
    cifa.push_back("//****--tok_command");
    if (LastChar != EOF)
      return gettok();
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  if (LastChar == '+') {
    cifa.push_back("+--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == '-') {
    cifa.push_back("---tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == '*') {
    cifa.push_back("*--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == '{') {
    cifa.push_back("{--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == '}') {
    cifa.push_back("}--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == '(') {
    cifa.push_back("(--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == ')') {
    cifa.push_back(")--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
  if (LastChar == ',') {
    cifa.push_back(",--tok_Symbol");
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
  }
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
  const std::string &getName() const { return Name; }
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
// VarExprAST - Expression class for referencing a many of 赋值statement.
class VarExprAST : public ExprAST {
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;

public:
  VarExprAST(
      std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames)
      : VarNames(std::move(VarNames)) {}

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
  yufa.push_back(space + "Var_Statement:\n");
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
  getNextToken(); // eat tok_VAR.
  // At least one variable name is required.
  if (CurTok != tok_var)
    return LogError("expected identifier after VAR");
  std::string IdName = IdentifierStr;
  getNextToken(); // eat identifierStr.
  std::unique_ptr<ExprAST> Init;
  VarNames.push_back(std::make_pair(IdName, std::move(Init)));
  return llvm::make_unique<VarExprAST>(std::move(VarNames));
}

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
  yufa.push_back(space + "Number_Statement:\n");
  auto Result = llvm::make_unique<NumberExprAST>(NumVal);
  getNextToken(); // consume the number
  return std::move(Result);
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); // eat (.
  yufa.push_back(space + "ParenExpr_Statement:\n");
  space += " ";

  yufa.push_back(space);
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken(); // eat ).
  space = space.substr(0, space.length() - 1);
  return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  yufa.push_back(space + "Identifier_Statement:\n");
  space += " ";
  std::string IdName = IdentifierStr;

  getNextToken(); // eat identifier.

  if (CurTok != '(') // Simple variable ref.
    return llvm::make_unique<VariableExprAST>(IdName);

  // Call.
  getNextToken(); // eat (
  std::vector<std::unique_ptr<ExprAST>> Args;
  if (CurTok != ')') {
    while (true) {
      yufa.push_back(space);
      if (auto Arg = ParseExpression()) {
        Args.push_back(std::move(Arg));
      }
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

  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}

//取负处理器
static std::unique_ptr<ExprAST> ParseFuExpr() {
  yufa.push_back(space + "FuExpr_Statement:\n");
  space += " ";
  auto Result = llvm::make_unique<NumberExprAST>(0);
  int FuTok = CurTok;
  getNextToken();
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseIdentifierExpr()));
  case tok_number:
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseNumberExpr()));
  case '(':
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return llvm::make_unique<BinaryExprAST>(FuTok, std::move(Result),
                                            std::move(ParseParenExpr()));
  }
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
  yufa.push_back(space + "Primary_Statement:\n");
  space += " ";
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return ParseIdentifierExpr();
  case tok_number:
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return ParseNumberExpr();
  case '(':
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return ParseParenExpr();
  case '-':
    yufa.push_back(space);
    space = space.substr(0, space.length() - 1);
    return ParseFuExpr();
  }
}

/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
  // If this is a binop, find its precedence.
  yufa.push_back(space + "BinOpRHS_Statement:\n");
  space += " ";
  while (true) {
    int TokPrec = GetTokPrecedence();

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec) {

      space = space.substr(0, space.length() - 1);
      return LHS;
    }

    // Okay, we know this is a binop.
    int BinOp = CurTok;
    getNextToken(); // eat binop

    // Parse the primary expression after the binary operator.
    yufa.push_back(space);
    auto RHS = ParsePrimary();
    if (!RHS)
      return nullptr;

    // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      yufa.push_back(space);
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
  yufa.push_back(space + "Expression_Statement:\n");
  space += " ";
  yufa.push_back(space);
  auto LHS = ParsePrimary();
  if (!LHS)
    return nullptr;
  yufa.push_back(space);
  space = space.substr(0, space.length() - 1);
  return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAST> ParseAssignment() {
  yufa.push_back(space + "Assignment_Statement:\n");
  space += " ";
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

  yufa.push_back(space);
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<BinaryExprAST>(
      '=', std::move(llvm::make_unique<VariableExprAST>(IdName)),
      std::move(ParseExpression()));
}

static std::unique_ptr<ExprAST> ParseIF() {
  yufa.push_back(space + "If_Statement:\n");
  space += " ";
  if (CurTok != tok_IF)
    return LogError("Expected IF in Expression");
  getNextToken();
  yufa.push_back(space);
  std::unique_ptr<ExprAST> ifexpr = ParseExpression();
  if (!ifexpr)
    return nullptr;
  if (CurTok != tok_THEN)
    return LogError("Expected THEN in Expression");
  getNextToken();
  yufa.push_back(space);
  std::unique_ptr<ExprAST> thenexpr = ParseStatement();
  if (!thenexpr)
    return nullptr;
  // getNextToken();
  std::unique_ptr<ExprAST> elseexpr;
  if (CurTok == tok_ELSE) {
    getNextToken();
    yufa.push_back(space);
    elseexpr = ParseStatement();
    // getNextToken();
  }

  if (CurTok != tok_FI)
    return LogError("Expected FI in Expression");
  getNextToken();

  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<IFExprAST>(std::move(ifexpr), std::move(thenexpr),
                                      std::move(elseexpr));
}

static std::unique_ptr<ExprAST> ParseWHILE() {
  yufa.push_back(space + "While_Statement:\n");
  space += " ";
  if (CurTok != tok_WHILE)
    return LogError("Expected WHILE in Expression");
  getNextToken();
  yufa.push_back(space);
  std::unique_ptr<ExprAST> whileexpr = ParseExpression();
  if (CurTok != tok_DO)
    return LogError("Expected DO in Expression");
  getNextToken();
  yufa.push_back(space);
  std::unique_ptr<ExprAST> doexpr = ParseStatement();
  // getNextToken();
  if (CurTok != tok_DONE)
    return LogError("Expected DONE in Expression");
  getNextToken();

  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<WHILEExprAST>(std::move(whileexpr),
                                         std::move(doexpr));
}
static std::unique_ptr<ExprAST> ParseCONTINUE() {
  yufa.push_back(space + "Continue_Statement:\n");
  space += " ";
  if (CurTok != tok_CONTINUE)
    return LogError("Expected CONTINUE in Expression");
  getNextToken();
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<NULLExprAST>();
}

static std::unique_ptr<ExprAST> ParseRETURN() {
  yufa.push_back(space + "Return_Statement:\n");
  space += " ";
  if (CurTok != tok_RETURN)
    return LogError("Expected RETURN in Expression");
  getNextToken();
  yufa.push_back(space);
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<RETURNExprAST>(std::move(ParseExpression()));
}

static std::unique_ptr<ExprAST> ParsePRINTITEM() {
  yufa.push_back(space + "PrintItem_Statement:\n");
  space += " ";
  if (CurTok != tok_text && CurTok != tok_number && CurTok != tok_var &&
      CurTok != '-' && CurTok != '(')
    return LogError("Expected epxr or string in Expression");
  std::unique_ptr<ExprAST> epxr;
  std::string text;
  if (CurTok == tok_text) {
    text = TEXT;
    getNextToken();
  } else {
    yufa.push_back(space);
    epxr = ParseExpression();
  }
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<PRINTITEMExprAST>(text, std::move(epxr));
}

static std::unique_ptr<ExprAST> ParsePRINT() {
  yufa.push_back(space + "Print_Statement:\n");
  space += " ";
  std::vector<std::unique_ptr<ExprAST>> items;
  if (CurTok != tok_PRINT)
    return LogError("Expected PRINT in Expression");
  getNextToken();
  if (CurTok != tok_text && CurTok != tok_number && CurTok != tok_var &&
      CurTok != '-' && CurTok != '(')
    return LogError("Expected epxr or string in Expression");
  yufa.push_back(space);
  items.push_back(ParsePRINTITEM());
  while (CurTok == ',') {
    getNextToken();
    yufa.push_back(space);
    items.push_back(ParsePRINTITEM());
  }
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<StarementsExprAST>(std::move(items));
}

static std::unique_ptr<ExprAST> ParseBlock() {
  yufa.push_back(space + "Block_Statement:\n");
  space += " ";
  std::vector<std::unique_ptr<ExprAST>> statements;
  if (CurTok != '{')
    return LogError("Expected '{' in Expression");
  getNextToken();
  while (CurTok == tok_VAR) {
    yufa.push_back(space);
    statements.push_back(ParseVARExpr());
  };

  while (CurTok == tok_var || CurTok == tok_RETURN || CurTok == tok_PRINT ||
         CurTok == tok_CONTINUE || CurTok == tok_IF || CurTok == tok_WHILE ||
         CurTok == '{') {
    yufa.push_back(space);
    statements.push_back(ParseStatement());
  };
  if (CurTok != '}')
    return LogError("Expected '}' in Expression");
  getNextToken();
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<StarementsExprAST>(std::move(statements));
}

static std::unique_ptr<ExprAST> ParseStatement() {
  yufa.push_back(space + "Statement_Statement:\n");
  space += " ";
  std::vector<std::unique_ptr<ExprAST>> statements;
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_var:
    yufa.push_back(space);
    statements.push_back(ParseAssignment());
    break;
  case tok_RETURN:
    yufa.push_back(space);
    statements.push_back(ParseRETURN());
    break;
  case tok_PRINT:
    yufa.push_back(space);
    statements.push_back(ParsePRINT());
    break;
  case tok_CONTINUE:
    yufa.push_back(space);
    statements.push_back(ParseCONTINUE());
    break;
  case tok_IF:
    yufa.push_back(space);
    statements.push_back(ParseIF());
    break;
  case tok_WHILE:
    yufa.push_back(space);
    statements.push_back(ParseWHILE());
    break;
  case '{':
    yufa.push_back(space);
    statements.push_back(ParseBlock());
    break;
  }
  space = space.substr(0, space.length() - 1);
  return llvm::make_unique<StarementsExprAST>(std::move(statements));
}
/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  yufa.push_back(space + "Prototype_Statement:\n");
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
  yufa.push_back(space+"FUNC_Statement:\n");
  space += " ";
  yufa.push_back(space);
  auto ProtoAST = ParsePrototype();
  if (!ProtoAST) {
    space = space.substr(0, space.length() - 1);
    return nullptr;
  }
  yufa.push_back(space);
  if (auto E = ParseStatement()) {
    // Make an anonymous proto.
    space = space.substr(0, space.length() - 1);
    return llvm::make_unique<FunctionAST>(std::move(ProtoAST), std::move(E));
  }
  space = space.substr(0, space.length() - 1);
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, AllocaInst *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<llvm::orc::KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static std::queue<std::string> que;

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
/// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
/// the function.  This is used for mutable variables etc.
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const std::string &VarName) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
                   TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(Type::getDoubleTy(TheContext), 0, VarName.c_str());
}

Value *NumberExprAST::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Unknown variable name");
  return Builder.CreateLoad(V, Name.c_str());
}

Value *BinaryExprAST::codegen() {
  // Special case '=' because we don't want to emit the LHS as an expression.
  if (Op == '=') {
    // Assignment requires the LHS to be an identifier.
    // This assume we're building without RTTI because LLVM builds that way by
    // default.  If you build LLVM with RTTI this can be changed to a
    // dynamic_cast for automatic error checking.
    VariableExprAST *LHSE = static_cast<VariableExprAST *>(LHS.get());
    if (!LHSE)
      return LogErrorV("destination of '=' must be a variable");
    // Codegen the RHS.
    Value *Val = RHS->codegen();
    if (!Val)
      return nullptr;

    // Look up the name.
    Value *Variable = NamedValues[LHSE->getName()];
    if (!Variable)
      return LogErrorV("Unknown variable name");

    Builder.CreateStore(Val, Variable);
    return Val;
  }
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
  for (auto &Arg : TheFunction->args()) {
    // Create an alloca for this variable.
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());

    // Store the initial value into the alloca.
    Builder.CreateStore(&Arg, Alloca);

    // Add arguments to variable symbol table.
    NamedValues[Arg.getName()] = Alloca;
  }

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

  Value *ElseV;
  if (ELSEExpr) {
    ElseV = ELSEExpr->codegen();
    if (!ElseV)
      return nullptr;
  } else { // If not specified, use 0.0.
    ElseV = ConstantFP::get(TheContext, APFloat(0.0));
  }

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
Value *VarExprAST::codegen() {
  std::vector<AllocaInst *> OldBindings;

  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  // Register all variables and emit their initializer.
  for (unsigned i = 0, e = VarNames.size(); i != e; ++i) {
    const std::string &VarName = VarNames[i].first;
    ExprAST *Init = VarNames[i].second.get();

    // Emit the initializer before adding the variable to scope, this prevents
    // the initializer from referencing the variable itself, and permits stuff
    // like this:
    //  var a = 1 in
    //    var a = a in ...   # refers to outer 'a'.
    Value *InitVal;
    if (Init) {
      InitVal = Init->codegen();
      if (!InitVal)
        return nullptr;
    } else { // If not specified, use 0.0.
      InitVal = ConstantFP::get(TheContext, APFloat(0.0));
    }

    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
    Builder.CreateStore(InitVal, Alloca);

    // Remember the old variable binding so that we can restore the binding when
    // we unrecurse.
    OldBindings.push_back(NamedValues[VarName]);

    // Remember this binding.
    NamedValues[VarName] = Alloca;
  }
  return nullptr;
}
Value *StarementsExprAST::codegen() {
  int count = Statements.size();
  if (count == 0) {
    return nullptr;
  }
  if (count == 1) {
    // if (typeid(Statements[0]) == typeid(RETURNExprAST))
    return Statements[0]->codegen();
  }
  for (int i = 0; i < count - 1; i++) {
    // if (typeid(Statements[i]) == typeid(RETURNExprAST)) {
    //   return Statements[i]->codegen();
    // }
    Statements[i]->codegen();
  }
  return Statements[count - 1]->codegen();
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
template <typename T> static std::string Print(T *value_or_type) {
  std::string str;
  llvm::raw_string_ostream stream(str);
  value_or_type->print(stream);
  return str;
}
typedef void (*print_int32_ptr_t)(int32_t);

llvm::Function *get_printf(llvm::Module *mod) {
  const char *fun_name = "printf";
  llvm::Function *func = mod->getFunction(fun_name);
  if (func == nullptr) {
    llvm::FunctionType *func_type = llvm::FunctionType::get(
        llvm::Type::getInt32Ty(mod->getContext()),
        {llvm::Type::getInt8PtrTy(mod->getContext())}, true);
    func = llvm::Function::Create(func_type, llvm::GlobalValue::ExternalLinkage,
                                  fun_name, mod);
  }
  return func;
}
Value *PRINTITEMExprAST::codegen() {
  auto printf_ptr = get_printf(TheModule.get());
  //llvm::raw_os_ostream os(std::cout);
  //TheModule->print(os, nullptr);

  if (!Expr) {
    Builder.CreateCall(printf_ptr, {Builder.CreateGlobalStringPtr(Text)});
   // que.push(Text);
        } 
  else {
            Builder.CreateCall(printf_ptr,
                               {Builder.CreateGlobalStringPtr("%d"),Expr->codegen()});
      //que.push(Print(Constant::getNullValue(Type::getDoubleTy(TheContext))));
        }
    return Constant::getNullValue(Type::getDoubleTy(TheContext));
}

Value *PRINTExprAST::codegen() {
  int count = Items.size();
if (count == 0) {
return nullptr;
}
if (count == 1) {
return Items[0]->codegen();
}
for (int i = 0; i < count - 1; i++) {
Items[i]->codegen();
}
return Items[count - 1]->codegen();
  return nullptr;
}
Value *RETURNExprAST::codegen() {
  //return Builder.CreateRet(Expr->codegen());
  return Expr->codegen();
}
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
  // Promote allocas to registers.
  TheFPM->add(createPromoteMemoryToRegisterPass());
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
      //int n = que.size();
      //for (int j = 0; j < n; j++) {
       // fprintf(stderr, que.front().c_str());
        //que.pop();
     // }
      fprintf(stderr, "\n");
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

  TheJIT = llvm::make_unique<llvm::orc::KaleidoscopeJIT>();

  InitializeModuleAndPassManager();
  // Run the main "interpreter loop" now.
  MainLoop();

  //输出词法分析结果
  FILE *fp;
  fp = fopen("cifa.txt", "w");
  //for (std::vector<std::string>::iterator cnt = cifa.begin(); cnt != cifa.end(); ++cnt) {
    //fprintf(fp, "%s", *cnt.c_str());
  //}
  for (int i = 0; i < cifa.size(); i++) {
    fprintf(fp, "%s\n", cifa[i].c_str());
  }
  fclose(fp);
  outs() << "Wrote " << "cifa.txt" << "\n";

  //输出语法分析结果
  fp = fopen("yufa.txt", "w");
  for (int i = 0; i < yufa.size(); i++) {
    fprintf(fp, "%s", yufa[i].c_str());
  }
  fclose(fp);
  outs() << "Wrote "
         << "yufa.txt"
         << "\n";

  // Initialize the target registry etc.
  InitializeAllTargetInfos();
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmParsers();
  InitializeAllAsmPrinters();

  auto TargetTriple = sys::getDefaultTargetTriple();
  TheModule->setTargetTriple(TargetTriple);

  std::string Error;
  auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);

  // Print an error and exit if we couldn't find the requested target.
  // This generally occurs if we've forgotten to initialise the
  // TargetRegistry or we have a bogus target triple.
  if (!Target) {
    errs() << Error;
    return 1;
  }

  auto CPU = "generic";
  auto Features = "";

  TargetOptions opt;
  auto RM = Optional<Reloc::Model>();
  auto TheTargetMachine =
      Target->createTargetMachine(TargetTriple, CPU, Features, opt, RM);

  TheModule->setDataLayout(TheTargetMachine->createDataLayout());

  auto Filename = "output.o";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }

  legacy::PassManager pass;
  auto FileType = TargetMachine::CGFT_ObjectFile;

  if (TheTargetMachine->addPassesToEmitFile(pass, dest, nullptr, FileType)) {
    errs() << "TheTargetMachine can't emit a file of this type";
    return 1;
  }

  pass.run(*TheModule);
  dest.flush();

  outs() << "Wrote " << Filename << "\n";
  return 0;
}
