package RegularExpression.Utils

import RegularExpression.Basic.*
import RegularExpression.Extended.RECD

import scala.language.implicitConversions

case object RexpUtils {
  private def charListToRexp(s: List[Char]) : Rexp = s match {
    case Nil => ONE
    case c::Nil => CHAR(c)
    case c::s => SEQ(CHAR(c), charListToRexp(s))
  }

  implicit def stringToRexp(s: String) : Rexp = charListToRexp(s.toList)
  implicit def rexpOps(r: Rexp): {
    def |(s: Rexp): ALT
    def % :STAR
    def ~(s: Rexp): SEQ
  } = new {
    def | (s: Rexp) = ALT(r, s)
    def % = STAR(r)
    def ~ (s: Rexp) = SEQ(r, s)
  }

  implicit def stringOps(s: String): {
    def |(r: String): ALT
    def % :STAR
    def ~(r: String): SEQ
  } = new {
    def | (r: String) = ALT(s, r)
    def % = STAR(s)
    def ~ (r: String) = SEQ(s, r)
  }

  implicit def stringRexpOps(s: String): {
    def |(r: Rexp): ALT
    def ~(r: Rexp): SEQ
    def $(r: Rexp): RECD
  } = new {
    def | (r: Rexp) = ALT(s, r)
    def ~ (r: Rexp) = SEQ(s, r)
    def $ (r: Rexp) = RECD(s, r)
  }
}
