//===--- RedundantPreprocessorCheck.cpp - clang-tidy ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "RedundantPreprocessorCheck.h"
#include "clang/Frontend/CompilerInstance.h"

namespace clang {
namespace tidy {
namespace readability {

namespace {
/// Gets the condition text of an #if directive from the the condition range's
/// source text.
std::string getCondition(StringRef SourceText) {
  // Take the first logical line of SourceText, i.e. ignore line ends where
  // the last character is a '\'.
  std::string Ret = SourceText;
  size_t Pos = 0;
  while (true) {
    Pos = Ret.find_first_of("\n", Pos);
    if (Pos == std::string::npos)
      break;
    else {
      if (Pos > 0 && Ret[Pos - 1] == '\\')
        Pos += 1;
      else {
        Ret = Ret.substr(0, Pos);
        break;
      }
    }
  }
  return Ret;
}

/// Information about an opening preprocessor directive.
struct PreprocessorEntry {
  SourceLocation Loc;
  /// Condition used after the preprocessor directive.
  std::string Condition;
};

class RedundantPreprocessorCallbacks : public PPCallbacks {
public:
  explicit RedundantPreprocessorCallbacks(ClangTidyCheck &Check,
                                          Preprocessor &PP)
      : Check(Check), PP(PP) {}

  void If(SourceLocation Loc, SourceRange ConditionRange,
          ConditionValueKind ConditionValue) override {
    // ConditionRange refers to the full range from the start of the #if
    // condition to the end of #endif. Extract just the condition of #if itself
    // from that, so we can compare that to other #if directives, similar to
    // #ifdef/#ifndef.
    StringRef SourceText =
        Lexer::getSourceText(CharSourceRange::getTokenRange(ConditionRange),
                             PP.getSourceManager(), PP.getLangOpts());
    std::string Condition = getCondition(SourceText);
    CheckMacroRedundancy(Loc, Condition, IfStack,
                         "nested redundant if; consider removing it",
                         "previous if was here", true);
  }

  void Ifdef(SourceLocation Loc, const Token &MacroNameTok,
             const MacroDefinition &MacroDefinition) override {
    std::string MacroName = PP.getSpelling(MacroNameTok);
    CheckMacroRedundancy(Loc, MacroName, IfdefStack,
                         "nested redundant ifdef; consider removing it",
                         "previous ifdef was here", true);
    CheckMacroRedundancy(Loc, MacroName, IfndefStack,
                         "nested redundant ifdef; consider removing it",
                         "previous ifndef was here", false);
  }

  void Ifndef(SourceLocation Loc, const Token &MacroNameTok,
              const MacroDefinition &MacroDefinition) override {
    std::string MacroName = PP.getSpelling(MacroNameTok);
    CheckMacroRedundancy(Loc, MacroName, IfndefStack,
                         "nested redundant ifndef; consider removing it",
                         "previous ifndef was here", true);
    CheckMacroRedundancy(Loc, MacroName, IfdefStack,
                         "nested redundant ifndef; consider removing it",
                         "previous ifdef was here", false);
  }

  void Endif(SourceLocation Loc, SourceLocation IfLoc) override {
    if (!IfStack.empty() && IfLoc == IfStack.back().Loc)
      IfStack.pop_back();
    if (!IfdefStack.empty() && IfLoc == IfdefStack.back().Loc)
      IfdefStack.pop_back();
    if (!IfndefStack.empty() && IfLoc == IfndefStack.back().Loc)
      IfndefStack.pop_back();
  }

private:
  void CheckMacroRedundancy(SourceLocation Loc, StringRef MacroName,
                            SmallVector<PreprocessorEntry, 4> &Stack,
                            StringRef Warning, StringRef Note, bool Store) {
    if (PP.getSourceManager().isInMainFile(Loc)) {
      for (const auto &Entry : Stack) {
        if (Entry.Condition == MacroName) {
          Check.diag(Loc, Warning);
          Check.diag(Entry.Loc, Note, DiagnosticIDs::Note);
        }
      }
    }

    if (Store)
      // This is an actual directive to be remembered.
      Stack.push_back({Loc, MacroName});
  }

  ClangTidyCheck &Check;
  Preprocessor &PP;
  SmallVector<PreprocessorEntry, 4> IfStack;
  SmallVector<PreprocessorEntry, 4> IfdefStack;
  SmallVector<PreprocessorEntry, 4> IfndefStack;
};
} // namespace

void RedundantPreprocessorCheck::registerPPCallbacks(
    CompilerInstance &Compiler) {
  Compiler.getPreprocessor().addPPCallbacks(
      ::llvm::make_unique<RedundantPreprocessorCallbacks>(
          *this, Compiler.getPreprocessor()));
}

} // namespace readability
} // namespace tidy
} // namespace clang
