import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ok8 {
  val random = new scala.util.Random()
  def havoc = random.nextInt
  @verify
  def test(b: Int) = {
    precondition(b >= 0)

    var a = b;
    if (b == 0) {
      assert(a == 0)
      a = havoc
      if (a == 0) {
        assert(a == 0)
      } else {
        a = b
      }
    } else {
      assert(a != 0)
      a = 0
    }
    assert(a == 0)
  }
}
