package RegularExpression.Extended

object CFUN_UTILS {
  val ALL: CFUN = CFUN(_ => true)

  def CHAR_FUN(c: Char) : CFUN = CFUN((d: Char) => c == d)
  def RANGE_FUN(s: Set[Char]) : CFUN = CFUN((c: Char) => s.contains(c))
}
