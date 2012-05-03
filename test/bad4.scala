import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object bada4 {
  class Queue(var data: Int, var next: Option[Queue])

  @verify
  def lock(l: Int) = {
    precondition(l == 0)
    val r = 1
    postcondition(r == 1)
    r
  }

  @verify
  def unlock(l: Int) = {
    precondition(l == 1)
    val r = 0
    postcondition(r == 0)
    r
  }

  @verify
  def foo() = {
    var l = 0
    var i = 3
    do {
      l = lock(l)
      if (i == 1) {
        l = unlock(l)
      }
      i -= 1
    } while (i != 0)
    l = unlock(l)
  }

  @verify
  def bar() = {
    var l = 0
    var i = 3
    while (i != 0) {
      l = lock(l)
      if (i == 1) {
        l = unlock(l)
      }
      i -= 1
    }
    l = unlock(l)
  }

  val random = new scala.util.Random()
  def boo() = random.nextInt == 0

  @verify
  def baz() = {
    var l = 0
    var i = 3
    do {
      l = lock(l)
      if (boo()) {
        l = unlock(l)
      }
      i -= 1
    } while (i != 0)
    l = unlock(l)
  }

  @verify
  def test(queue: Queue) {
    var l = 0

    var oldi = 0
    var newi = 0
    var q = queue

    do {
      l = lock(l)

      oldi = newi

      if (q.next != None) {
        q = q.next.get
        q.data = newi

        //assert(newi == oldi)
        l = unlock(l)

        //bad: missing newi += 1
      }

      //assert((l == 0 && newi != oldi) || (l == 1 && newi == oldi))
    } while (newi != oldi)

    l = unlock(l)
  }
}
