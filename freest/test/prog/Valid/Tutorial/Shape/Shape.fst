type Point = (Float, Float)
type Radius = Float

-- type Shape: *T
data Shape = Circle Point Radius
           | Rectangle Point Point
           | Triangle Point Point Point

area : Shape -> Float
area (Circle _ r) =
    pi *. r *. r
area (Rectangle (x1, y1) (x2, y2)) =
    absF (x2 -. x1) *. absF (y2 -. y1)
area (Triangle (x1, y1) (x2, y2) (x3, y3)) =
    absF (x1 *. (y2 -. y3) +. x2 *. (y3 -. y1) +. x3 *. (y1 -. y2)) /. 2.0

area' : Shape -> Float
area' shape =
    case shape of
        Circle p r -> pi *. r *. r
        Rectangle (x1, y1) (x2, y2) -> absF (x2 -. x1) *. absF (y2 -. y1)
        Triangle (x1, y1) (x2, y2) (x3, y3) -> absF (x1 *. (y2 -. y3) +. x2 *. (y3 -. y1) +. x3 *. (y1 -. y2)) /. 2.0

aTriangle : Shape
aTriangle = Triangle (0.0, 0.0) (1.0, 0.0) (0.0, 1.0)

_ = print (area aTriangle)

_ = print (area' aTriangle -. area aTriangle <. 0.0001)