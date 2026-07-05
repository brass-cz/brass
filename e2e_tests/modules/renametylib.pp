// Library whose record type is imported under a rename by rename_type.pp.
type Vec2 = {
    x: float64
    y: float64
}

fun Vec2.new(x: float64, y: float64) {
    return Self { x: x, y: y }
}

fun Vec2.add(self, o: Vec2) {
    return Vec2 { x: self.x + o.x, y: self.y + o.y }
}
