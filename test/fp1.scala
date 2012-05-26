import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object fp1 {
  class Queue(var data: Int, var next: Option[Queue], var locker: Locker)

  @verify
  class Locker {
    var l = 0

    @verify
    def lock() {
      precondition(l == 0)
      l = 1
      postcondition(l == 1)
    }

    @verify
    def unlock() = {
      precondition(l == 1)
      l = 0
      postcondition(l == 0)
    }

    @verify
    def test(queue: Queue) {
      precondition(l == 0)

      var oldi = 0
      var newi = 0
      var q = queue

      do {
        lock()

        oldi = newi

        if (q.next != None) {
          q = q.next.get
          q.data = newi
          // q.locker.lock() <- complains about verified method call on non-field qualifier
          q.locker.l = 0 // BAD if q.locker == this
          // q.messWithLocker() <- and hard to detect b/c it could be indirect ...

          assert(newi == oldi)
          unlock()

          newi += 1
        }

        assert((l == 0 && newi != oldi) || (l == 1 && newi == oldi))
      } while (newi != oldi)

      unlock()
      postcondition(l == 0)
    }
  }
}
