package lazabs.types


sealed abstract class Type
case class UnitType() extends Type
case class IntegerType() extends Type
case class BooleanType() extends Type
case class StringType() extends Type
case class AnyType() extends Type

trait ScalaType {
	self =>      // this-aliasing
	private var _stype: Type = UnitType()
	// Getter
	def stype  = _stype
	// Setter
	def stype( value: Type): self.type = {
		_stype = value
		self
	}
}
