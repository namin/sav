import net.namin.sav.annotation.verify

object ex1 {
  val random = new scala.util.Random()
  def havoc = random.nextInt
  @verify
  def test(b: Int) = {
    assume(b >= 0)
    var P1:Int = 0
    var P2:Int = 0
    var a: Int = b    
    var h: Int = 0
    assert(a + P1 + P2 == b && a >= 0)
    while(a > 0) {
      h = havoc
      if(h >= 0) P1 = P1 + 1 else P2 = P2 + 1  
      a = a - 1
    }
    assert(P1 + P2 == b)
  }
}
