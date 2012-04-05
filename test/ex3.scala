object ex3 {
  def test(length: Int) {
    assume(length > 0)
    var i: Int = 0
    var j: Int = 1
    assert(j <= length)
    while(j < length) {
      assert(j < length)
      i = j - 1
      assert(j < length)
      while(i >= 0) {
        assert(j < length)
        i = i - 1        
      }
      assert(j < length)
      j = j + 1
    }
    assert(j == length)    
  }
}
