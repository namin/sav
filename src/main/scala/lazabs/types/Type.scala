package lazabs.types


sealed abstract class Type
case class UnitType() extends Type
case class IntegerType() extends Type
case class BooleanType() extends Type
case class StringType() extends Type
case class AnyType() extends Type
case class ArrayType(t: Type) extends Type
case class SetType(t: Type) extends Type
case class ActorType extends Type
case class ClassType(id: String) extends Type

trait ScalaType {
	self =>      // this-aliasing
	private var _stype: Type = IntegerType() // by default
	// Getter
	def stype  = _stype
	// Setter
	def stype( value: Type): self.type = {
		_stype = value
		self
	}
}