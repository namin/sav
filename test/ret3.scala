import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ret3 {
  @verify
  def test(a: Int): Int = {
    var x = 0
    assert(x == 0)
    while (a == 0) {
      x = 1
      return x
    }
    assert(x == 0)
    x
  }
}
