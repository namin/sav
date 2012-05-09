import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ret4 {
  @verify
  def test(a: Int): Int = {
    var x = 0
    do {
      x = 1
      return x
    } while (a == 0)
    // unreachable assert
    assert(x == 0)
    x
  }
}
