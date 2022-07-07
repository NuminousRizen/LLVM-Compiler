import $file.tokeniser, tokeniser._

import scala.language.implicitConversions    
import scala.language.reflectiveCalls


// Parser combinators
//    type parameter I needs to be of Seq-type.
//
abstract class Parser[I, T](implicit ev: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(_._2.isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { 
	println (s"Parse Error\n${err.minBy(_._2.length)}") ; sys.exit(-1) 
    }
    }
}

// Convenience for writing grammar rules.
case class ~[+A, +B](_1: A, _2: B)

class SeqParser[I, T, S](p: => Parser[I, T], 
                         q: => Parser[I, S])(implicit ev: I => Seq[_]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I, T](p: => Parser[I, T], 
                      q: => Parser[I, T])(implicit ev: I => Seq[_]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I, T, S](p: => Parser[I, T], 
                         f: T => S)(implicit ev: I => Seq[_]) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

// Convenient combinators.
implicit def ParserOps[I, T](p: Parser[I, T])(implicit ev: I => Seq[_]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

def ListParser[I, T, S](p: => Parser[I, T], 
                        q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)) ==> { case x ~ _ ~ z => x :: z : List[T] } ||
  (p ==> ((s) => List(s)))
}

case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) = TokParser(t)

implicit def TokOps(t: Token) = new {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def ==>[S] (f: => Token => S) = new FunParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object IntParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_INT(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object FloatParser extends Parser[List[Token], Float] {
  def parse(ts: List[Token]) = ts match {
    case T_FLOAT(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object CharacterParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_CHAR(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object ArgsParser extends Parser[List[Token], (String, String)] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(n)::T_COLON::T_TYPE(t)::ts => Set(((n, t), ts))
    case _ => Set ()
  }
}

case object TypeParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_TYPE(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String , String)], ty: String , body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String , v: Int) extends Decl
case class FConst(name: String , x: Float) extends Decl

case class Call(name: String , args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp // Integer numbers.
case class FNum(i: Float) extends Exp // Floating numbers.
case class ChConst(c: Int) extends Exp // Char constants (As ASCII int).
case class Aop(o: String , a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp

case class Bop(o: String , a1: Exp, a2: Exp) extends BExp

// Expressions.
lazy val Exp: Parser[List[Token], Exp] = 
    (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Exp ~ T_KWD("else") ~ Exp) ==>
        { case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
    (T_PAREN("{") ~ Exp ~ T_PAREN("}")) ==>
        { case _ ~ x ~ _ => x: Exp } ||
    (L ~ T_SEMI ~ Exp) ==> { case x ~ _ ~ y => Sequence(x, y): Exp } || L
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp) ==> { case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp) ==> { case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T) ==> { case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T) ==> { case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T) ==> { case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_PAREN("(") ~ ListParser(Exp, T_COMMA) ~ T_PAREN(")")) ==> 
    { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
    (IdParser ~ T_PAREN("(") ~ T_PAREN(")")) ==> 
    { case x ~ _ ~ _ => Call(x, Nil): Exp } ||
  (T_PAREN("(") ~ Exp ~ T_PAREN(")")) ==> { case _ ~ y ~ _ => y: Exp } || 
  IdParser ==> { case x => Var(x): Exp } || 
  IntParser ==> { case x => Num(x): Exp } ||
  FloatParser ==> { case x => FNum(x): Exp } ||
  CharacterParser ==> { case x => ChConst(x): Exp }

// Boolean Expressions.
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP("=>") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", z, x): BExp }  

// Declarations.
lazy val Decl: Parser[List[Token], Decl] =
    (T_KWD("def") ~ IdParser ~ T_PAREN("(") ~ ListParser(ArgsParser, T_COMMA) ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==>
        {case _ ~ defName ~ _ ~ defArgs ~ _ ~ _ ~ defType ~ _ ~ defExp => Def(defName, defArgs, defType, defExp) : Decl} ||
    (T_KWD("def") ~ IdParser ~ T_PAREN("(") ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp) ==>
        {case _ ~ defName ~ _ ~ _ ~ _ ~ defType ~ _ ~ defExp => Def(defName, Nil, defType, defExp) : Decl} ||
    (T_KWD("val") ~ IdParser ~ T_COLON ~ T_TYPE("Int") ~ T_OP("=") ~ IntParser) ==>
        {case _ ~ constName ~ _ ~ _ ~ _ ~ constInt => Const(constName, constInt) : Decl} ||
    (T_KWD("val") ~ IdParser ~ T_COLON ~ T_TYPE("Double") ~ T_OP("=") ~ FloatParser) ==> 
        {case _ ~ constName ~ _ ~ _ ~ _ ~ constFloat => FConst(constName, constFloat) : Decl}

// Program.
lazy val Prog: Parser[List[Token], List[Decl]] =
  (Decl ~ T_SEMI ~ Prog) ==> { case x ~ _ ~ z => x :: z : List[Decl] } ||
  (Exp ==> ((s) => List(Main(s)) : List[Decl]))