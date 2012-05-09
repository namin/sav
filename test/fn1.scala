import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object fn1 {
  def alwaysTrue() = true
  @verify
  def test() = {
    var x = 0
    if (alwaysTrue()) {
      x += 1
    }
    if (alwaysTrue()) {
      x -= 1
    }
    postcondition(x == 0)
    x
  }
}
