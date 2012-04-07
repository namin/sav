import net.namin.sav.annotation.verify

object ex3 {
  @verify
  def test(length: Int) {
    assume(length > 0)
    var i: Int = 0
    var j: Int = 1
    assert(j <= length)
    while(j < length) {
      i = j - 1
      assert(j < length)
      while(i >= 0) {
        i = i - 1        
      }
      j = j + 1
    }
    assert(j == length)    
  }
}
