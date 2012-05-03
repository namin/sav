import net.namin.sav.annotation.verify

object ex2 {
  @verify
  def test(a: Int, b: Int, c: Int) {
    var isoscles: Int = 0
    var scalene: Int = 0
    var triangle: Int = 0
    var equilateral: Int = 0
    isoscles = 0
    scalene = 0
    triangle = 0
    equilateral = 0
    if (a > 0 && b > 0 && c > 0 && a < b + c) {
      triangle = 1
    } else {
      triangle = -1
    }
    if (a >= b) {
      if ( b >= a) {
        isoscles = 1
      }
    }
    if (b >= c) {
      if (c >= b) {
        isoscles = 1
      }
    }
    if (a >= b) {
      if (b >= c) {
        if (c >= a) {
          equilateral = 1
        }
      }
    }
    if (a < b + c) {
      if (isoscles == 0 || equilateral == 0) {
        scalene = 1
      }
    }
    if (triangle == 1) {
      if (equilateral == 1) {
        assert(isoscles == 1 && scalene == 0)
      } else {
        if (isoscles == 0) {
          assert(scalene == 1)
        }
      }
    }
  }
}
