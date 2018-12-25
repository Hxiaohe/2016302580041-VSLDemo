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
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
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
