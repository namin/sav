import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object inv2 {
  @verify
  class Foo {
    var x = 0

    @verify
    def bar(y: Int) {
      x = y
      val _ = evil(this)
      // postcondition is false if y!=0 
      postcondition(x == y)
    }
  }

  def evil(foo: Foo) {
    foo.x = 0
  }
}
