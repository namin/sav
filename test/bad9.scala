import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object bad9 {
  @verify
  class Foo {
    var x = 0

    @verify
    def test(y: Int) {
      precondition(y >= 0)
      x = 0
      for (i <- 0 to y) {
        x += 1
      }
      postcondition(x == 0)
    }
  }
}
