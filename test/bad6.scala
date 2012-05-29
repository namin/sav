import net.namin.sav.annotation.verify
import net.namin.sav.lib._

object ok6 {

  @verify
  def even(n: Int): Int = {
    precondition(n >= 0)
    var r = 0
    if (n == 0) r = 1
    else if (n == 1) r = 0
    else if (n == 2) r = 2 // bad ...
    else r = odd(n-1)
    postcondition(r == 0 || r == 1)
    r
  }

  @verify
  def odd(n: Int): Int = {
    precondition(n >= 0)
    var r = 0
    if (n == 0) r = 0
    else if (n == 1) r = 1
    else r = even(n-1)
    postcondition(r == 0 || r == 1)
    r
  }
}
