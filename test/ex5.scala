import net.namin.sav.annotation.verify

object ex5 {
  @verify
  def test(a: Int) = {
    var b = 0
    if (a < 0) b = -a
    else b = a
    assert(b >= 0)
  }
}
