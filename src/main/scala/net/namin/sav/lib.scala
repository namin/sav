package net.namin.sav

object lib {
  def precondition(b: Boolean) = assume(b)
  def postcondition(b: Boolean) = assert(b)
  def old[T](x: T) = x
}
