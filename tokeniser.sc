import scala.collection.immutable.Set

abstract class Rexp

// Some basic regular expressions.
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

// Optional/Extended regular expressions.
case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp

case class CFUN(f: Char => Boolean) extends Rexp

case class RECD(x: String, r: Rexp) extends Rexp

val ALL = CFUN((c: Char) => true)

def CHAR_FUN(c: Char) : CFUN = CFUN((d: Char) => c == d)

def RANGE_FUN(s: Set[Char]) : CFUN = CFUN((c: Char) => s.contains(c))

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val

case class Range(c: Char) extends Val
case class CFun(c: Char) extends Val
case class Plus(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class NTimes(vs: List[Val]) extends Val

case class Rec(x: String, v: Val) extends Val


// Some functions that make writing regular expressions easier.
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// NOTE: nullable and der are based on the Brzozowski algorithm.

// Tests whether the regular expression can recognise 
// the empty string.
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true

  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)

  case CFUN(_) => false

  case RECD(_, r1) => nullable(r1)
}

// The derivative of a regular expression w.r.t. a character.
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))

  case RANGE(s) => if (s.contains(c)) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))

  case CFUN(f) => if (f(c)) ONE else ZERO

  case RECD(_, r1) => der(c, r1)
}

// Extracts a string from a value.
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString

  case Range(c) => c.toString
  case CFun(c) => c.toString
  case Plus(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case NTimes(vs) => vs.map(flatten).mkString

  case Rec(_, v) => flatten(v)
}

// Extracts an environment from a value;
// used for tokenising a string.
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)

  case Range(c) => Nil
  case CFun(c) => Nil
  case Plus(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case NTimes(vs) => vs.flatMap(env)

  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The injection and mkeps part of the lexer.
// This part is based on the Sulzmann & Lu method.
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)

  case RANGE(s) => throw new Exception("Range is not nullable")
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => Optional(Empty)
  case NTIMES(r, n) =>
    if(n == 0) Stars(Nil)
    else Stars(List.fill(n)(mkeps(r)))

  case RECD(x, r) => Rec(x, mkeps(r))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c)

  case (RANGE(d), Empty) => Chr(c)
  case (CFUN(f), Empty) => CFun(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v) => Optional(inj(r, c, v))
  case (NTIMES(r, n), Sequ(v1, Stars(v2))) => Stars(inj(r, c, v1)::v2)

  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

// Some "rectification" functions for simplification.
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))

def F_ERROR(v: Val): Val = throw new Exception("error")

// Simplification.
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// Lexing functions including simplification.
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") }
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// Defining language syntax.
val KEYWORD : Rexp = "if" | "then" | "else" | "def" | "val"
val TYPE : Rexp = "Int" | "Double" | "Void"
val OPERATOR : Rexp = "=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val LETTER : Rexp = CFUN((c: Char) => ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".contains(c)))
val SYMBOL : Rexp = LETTER | CFUN((c: Char) => ("""._><=;,\:-""".contains(c)))
val DIGIT : Rexp = CFUN((c: Char) => "0123456789".contains(c))
val WHITESPACE : Rexp = PLUS(" " | "\n" | "\t" | "\r")
val STRING : Rexp = "\"" ~ (SYMBOL | WHITESPACE | DIGIT).% ~ "\""
val CHARACTER : Rexp = "\'" ~ (SYMBOL | WHITESPACE | DIGIT) ~ "\'"
val PARENTHESES : Rexp = "(" | "{" | "}" | ")"
val SEMICOLON : Rexp = ";"
val IDENTIFIER : Rexp = LETTER ~ ("_" | LETTER | DIGIT).%
val DIGIT0 : Rexp = CFUN((c: Char) => "0123456789".contains(c))
val DIGIT1 : Rexp = CFUN((c: Char) => "123456789".contains(c))
val INTEGER : Rexp = OPTIONAL("-") ~ ((DIGIT1 ~ DIGIT0.%) | "0")
val FLOAT : Rexp = INTEGER ~ "." ~ DIGIT0.%
val COLON : Rexp = ":"
val COMMA : Rexp = ","
val ALL1 = SYMBOL | DIGIT | OPERATOR | " " | ":" | ";" | "\"" | "=" | "," | "(" | ")"
val ALL2 = ALL1 | "\n"
val COMMENT = ("/*" ~ ALL2.% ~ "*/") | ("//" ~ ALL1.% ~ "\n")

val FUN_REGS = (("Keyword" $ KEYWORD) |
                  ("Type" $ TYPE) |
                  ("Identifier" $ IDENTIFIER) |
                  ("Operator" $ OPERATOR) |
                  ("Comment" $ COMMENT) |
                  ("Semicolon" $ SEMICOLON) |
                  ("Colon" $ COLON) |
                  ("Comma" $ COMMA) |
                  ("Character" $ CHARACTER) |
                  ("String" $ STRING) |
                  ("Parentheses" $ PARENTHESES) |
                  ("Integer" $ INTEGER) |
                  ("Float" $ FLOAT) |
                  ("Whitespace" $ WHITESPACE)).%

// Tokeniser.
abstract class Token 
case object T_SEMI extends Token
case object T_COLON extends Token
case object T_COMMA extends Token

case class T_KWD(s: String) extends Token
case class T_ID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STR(s: String) extends Token
case class T_CHAR(n: Int) extends Token
case class T_INT(n: Int) extends Token
case class T_FLOAT(n: Float) extends Token
case class T_TYPE(s: String) extends Token
case class T_PAREN(s: String) extends Token

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

// This function strips away the "" from a string token and processes all the escape characters.
// Meaning if there was a \n it would be a newline instead of a string.
def stringTokenPretty(s: String): String = {
  if(s.length > 1) StringContext.processEscapes(s.substring(1, s.length - 1))
  else StringContext.processEscapes(s)
}

// Only keep tokens we are interested in (e.g. ignore whitespaces and comments).
val token : PartialFunction[(String, String), Token] = {
  case ("Semicolon", _) => T_SEMI
  case ("Parentheses", s) => T_PAREN(s)
  case ("Identifier", s) => T_ID(s)
  case ("Operator", s) => T_OP(s)
  case ("Integer", s) => T_INT(s.toInt)
  case ("Float", s) => T_FLOAT(s.toFloat)
  case ("Keyword", s) => T_KWD(s)
  case ("Character", s) => T_CHAR(stringTokenPretty(s)(0).toInt)
  case ("String", s) => T_STR(stringTokenPretty(s))
  case ("Colon", _) => T_COLON
  case ("Comma", _) => T_COMMA
  case ("Type", s) => T_TYPE(s)
}

// By using collect we filter out all unwanted tokens.
def tokenise(s: String) : List[Token] = {
  lexing_simp(FUN_REGS, StringContext.processEscapes(s)).collect(token)
}