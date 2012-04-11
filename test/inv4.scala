import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object inv4 {
  @verify
  class Foo {
    var x = 0

    @verify
    def reset() {
      x = 0
    }
  }

  @verify
  class Bar {
    val foo = new Foo

    @verify
    def baz() {
      foo.x = 1
      foo.reset()
      // postcondition is always false
      postcondition(foo.x == 1)
    }
  }
}
