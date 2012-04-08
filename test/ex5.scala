import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ex5 {
  @verify
  def abs(a: Int) = {
    var b = 0
    if (a < 0) b = -a
    else b = a
    postcondition(b >= 0)
    b
  }
}
