object ex5 {
  def test(a: Int) = {
    var b = 0
    if (a < 0) (b = -a) else  (b = a)
    assert(b >= 0)
  }
}
