import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object inv3 {
  @verify
  class Foo {
    var x = 0
  }

  @verify
  class Bar {
    val foo = new Foo

    @verify
    def baz() {
      val foo_alias = foo
      foo.x = 1
      foo_alias.x = 2
      // postcondition is always false
      postcondition(foo.x == 1)
    }
  }
}
