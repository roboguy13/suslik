package org.tygus.suslik.parsing

import scala.util.parsing.combinator.lexical.StdLexical

/**
  * @author Ilya Sergey
  */
class SSLLexical extends StdLexical {

  // Add keywords
  reserved += ("if", "then", "else", "true", "false", "emp", "not", "return", "predicate", "synonym", "in", "lower", "upper")
  reserved += ("error","magic","malloc", "free", "let", "assume")
  reserved += ("with")
  reserved += ("null")

  // Types
  reserved += ("int", "bool", "pred", "func", "any", "loc", "set", "void", "interval")

  delimiters += ("(", ")", "=", ";", "**", "*", ":->", ":=>", "=i", "<=i", "++", "--", "..",
      "{", "}", "/\\", "&&", "\\/", "||", "\n", "\r", "=>", "?", ":",
      "<", ">", ",", "/",   "+", "-", "==", "!=", "==>", "<=", ">=", "[", "]", "|", "??"
  )

}
