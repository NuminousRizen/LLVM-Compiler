@ import $file.tokeniser, tokeniser._
@ import $file.parser, parser._

import os._

// For generating new labels.
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS (intermediate) language for FUN.
abstract class KExp
abstract class KVal

case class KVar(s: String , ty: String = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(i: Float) extends KVal
case class KChConst(i: Int) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KGlobalVar(s: String) extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp

def typ_val(v: KVal, ts: Map[String, String]) : String = v match {
  case KVar(s, t) => ts.getOrElse(s, t)
  case KGlobalVar(s) => ts.getOrElse(s, "UNDEF")
  case KNum(_) => "Int"
  case KFNum(_) => "Double"
  case KChConst(_) => "Int"
  case Kop("=", v1, v2) => typ_val(v2, ts)
  case Kop(_, v1, v2) => {
    val typ_v1 = typ_val(v1, ts)
    val typ_v2 = typ_val(v2, ts)
    if (typ_v1 == typ_v2) typ_v1 else "UNDEF"
  }
  case KCall(o, _) => ts.getOrElse(o, "UNDEF")
}
def typ_exp(a: KExp, ts: Map[String, String]) : String = a match {
  case KLet(x, e1, e2) => typ_exp(e2, ts + (x -> typ_val(e1, ts)))
  case KIf(x, e1, e2) => {
    val typ_e1 = typ_exp(e1, ts)
    val typ_e2 = typ_exp(e2, ts)
    if (typ_e1 == typ_e2) typ_e1 else "UNDEF"
  }
  case KReturn(v) => typ_val(v, ts)
}

def isVarGlobal(s: String) : Boolean = {
  s(0).isUpper
}

// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => {
    if(isVarGlobal(s)) {
      val z = Fresh("tmp")
      KLet(z, KGlobalVar(s), k(KVar(z)))
    }
    else {
      k(KVar(s))
    }
  }
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case ChConst(i) => k(KChConst(i))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
}

def CPSi(e: Exp) = CPS(e)(KReturn)

// Convenient string interpolations 
// for instructions, labels and methods.
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

def compile_type(s: String) : String = s match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Void" => "void"
  case _ => s
}

def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "%" => "srem i32"
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 " // Signed less or equal.
  case "<" => "icmp slt i32 " // Signed less than.
}


def compile_dop(op: String) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "%" => "frem double"
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
}

// Compile K values.
def compile_val(v: KVal)(typeEnv: Map[String, String]) : String = v match {
  case KNum(i) => s"$i"
  case KFNum(i) => s"$i"
  case KChConst(i) => s"$i"
  case KVar(s, _) => {
    if (typeEnv.getOrElse(s, "UNDEF") == "Void") ""
    else s"%$s"
  }
  case KGlobalVar(s) => {
    val variable_type = compile_type(typeEnv.getOrElse(s, "UNDEF"))
    s"load $variable_type, $variable_type* @$s"
  }
  case Kop(op, x1, x2) => 
    if(typ_val(v, typeEnv) == "Int") s"${compile_op(op)} ${compile_val(x1)(typeEnv)}, ${compile_val(x2)(typeEnv)}"
    else s"${compile_dop(op)} ${compile_val(x1)(typeEnv)}, ${compile_val(x2)(typeEnv)}"
  case KCall(x1, args) => {
    def compile_call_args(a: List[KVal]) : String = a match {
      case Nil => ""
      case h::tl => {
        compile_type(typ_val(h, typeEnv)) ++ " " ++ compile_val(h)(typeEnv) ++ ", " ++ compile_call_args(tl)
      }
    }
    s"call ${compile_type(typeEnv.getOrElse(x1, "UNDEF"))} @$x1 (${compile_call_args(args).dropRight(2)})"
  }
}

def isCallVoid(v: KCall, typeEnv: Map[String, String]) : Boolean = v match {
  case KCall(x1, args) => {
    typeEnv.getOrElse(x1, "UNDEF") == "Void"
  }
}

// Compile K expressions.
def compile_exp(a: KExp)(typeEnv: Map[String, String]) : String = a match {
  case KReturn(v) =>
    i"ret ${compile_type(typ_exp(a, typeEnv))} ${compile_val(v)(typeEnv)}"
  case KLet(x: String, v: KVal, e: KExp) => v match {
    case KCall(x1, vrs) => {
      if (isCallVoid(KCall(x1, vrs), typeEnv)) i"${compile_val(v)(typeEnv)}" ++ compile_exp(e)(typeEnv + (x -> "Void"))
      else i"%$x = ${compile_val(v)(typeEnv)}" ++ compile_exp(e)(typeEnv + (x -> typ_val(v, typeEnv)))
    }
    case _ => i"%$x = ${compile_val(v)(typeEnv)}" ++ compile_exp(e)(typeEnv + (x -> typ_val(v, typeEnv)))
  }
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1)(typeEnv) ++
    l"\n$else_br" ++ 
    compile_exp(e2)(typeEnv)
  }
}

def compile_args(args: List[(String, String)]) : String = args match {
  case Nil => ""
  case h::tl => compile_type(h._2) ++ " %" ++ h._1 ++ ", " ++ compile_args(tl)
}

def update_type_env_params(args: List[(String, String)], typeEnv: Map[String, String]) : Map[String, String] = args match {
  case Nil => Map()
  case h::tl => (typeEnv + (h._1 -> h._2)) ++ update_type_env_params(tl, typeEnv)
}

// Compile function for declarations and main.
def compile_decl(d: Decl)(typeEnv: Map[String, String]) : (String, Map[String, String]) = d match {
  case Def(name, args, ty, body) => {
    (m"define ${compile_type(ty)} @$name (${compile_args(args).dropRight(2)}) {" ++
    compile_exp(CPSi(body))(typeEnv + (name -> ty) ++ update_type_env_params(args, typeEnv)) ++
    m"}\n", typeEnv + (name -> ty))
  }
  case Main(body) => {
    (m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0))))(typeEnv) ++
    m"}\n", typeEnv)
  }
  case Const(name, v) => {
    if(isVarGlobal(name)) (i"@$name = global i32 $v", typeEnv + (name -> "Int"))
    else (i"%$name = i32 $v", typeEnv + (name -> "Int"))
  }
  case FConst(name, v) => {
    if(isVarGlobal(name)) (i"@$name = global double $v", typeEnv + (name -> "Double"))
    else (i"%$name = double $v", typeEnv + (name -> "Double"))
  }
}

def compile(prog: List[Decl], typeEnv: Map[String, String]) : String = prog match {
  case Nil => ""
  case h::tl => {
    val (compiled_decl, updatedEnv) = compile_decl(h)(typeEnv)
    compiled_decl ++ compile(tl, updatedEnv)
  }
}

val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

@.str_char = private constant [3 x i8] c"%c\00"

define void @print_char(i32 %x) {
   %t0 = getelementptr [3 x i8], [3 x i8]* @.str_char, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

@.str = private constant [3 x i8] c"%d\00"

define void @print_int(i32 %x) {
   %t0 = getelementptr [3 x i8], [3 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)
"""


// The initial environment, this contains the 'types' for the prelude functions.
val INITIAL_ENVIRONMENT = Map(("new_line" -> "Void"), 
                              ("print_star" -> "Void"),
                              ("print_space" -> "Void"),
                              ("skip" -> "Void"),
                              ("print_int" -> "Void"),
                              ("print_char" -> "Void"))

def compile_program(prog: List[Decl]) : String = 
  prelude ++ compile(prog, INITIAL_ENVIRONMENT)

// Handy function for generating .ll files.
@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = Prog.parse_single(tks)
    val code = compile_program(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}