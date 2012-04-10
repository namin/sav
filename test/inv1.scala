import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object inv1 {
  @verify
  class Foo {
    var x = 0

    @verify
    def bar(y: Int, foo: Foo) {
      x = y
      foo.x = 0
      // postcondition is false if y!=0 and foo==this
      postcondition(x == y)
    }

    @verify
    def evil() {
      bar(1, this)
      postcondition(x == 1)
    }
  }
}
