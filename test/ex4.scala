import net.namin.sav.annotation.verify

object ex4 {
  class Queue(var data: Int, var next: Option[Queue])

  def lock() = 1
  def unlock() = 0

  @verify
  def test(queue: Queue) {
    var locked = 0

    var oldi = 0
    var newi = 0
    var q = queue

    do {
      assert(locked == 0)
      locked = lock()
      assume(locked == 1)

      oldi = newi

      if (q.next != None) {
        q = q.next.get
        q.data = newi

        assert(locked == 1 && newi == oldi)
        locked = unlock()
        assume(locked == 0)

        newi += 1
      }

      assert((locked == 0 && newi != oldi) || (locked == 1 && newi == oldi))
    } while (newi != oldi)

    assert(locked == 1)
    locked = unlock()
    assume(locked == 0)
  }
}
