import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ret1 {
  @verify
  def test(a: Int): Int = {
    var x = a
    if (a == 0) {
      x = 0
      // cannot use return with postcondition
      return 1
    } else {
      x = 0
    }
    postcondition(x == 0)
    x
  }
}
