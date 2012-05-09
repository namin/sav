import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ret2 {
  @verify
  def test(a: Int): Int = {
    var x = a
    if (a == 0) {
      x = 1
      return x
    } else {
      x = 0
    }
    assert(x == 0)
    x
  }
}
