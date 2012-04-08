import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object neg1 {
  @verify
  def mult(x: Int, y: Int) = {
    precondition(x >= 0 && y >= 0)
    var r = 0
    var i = 0
    assert(i <= y && r + (y-i)*x == y*x)
    while (i < y) {
       i = i + 1
       r = r + x
     }
    postcondition(r == x * y)
    r
  }
}
