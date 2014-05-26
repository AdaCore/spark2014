with Formal.Numerics.Elementary_Functions;
use Formal.Numerics.Elementary_Functions;

package body Spaces.Positions is

   function Create return Position is
   begin
      return (x => 0.0, y => 0.0);
   end Create;

   function Create (x_in, y_in : Float) return Position is
   begin
      return (x => x_in, y => y_in);
   end Create;

   function Create (theta : Angle) return Position is
   begin
      return (x =>  Cos (dCast (theta)), y =>  Sin (dCast (theta)));
   end Create;

   function Create (d : Float; theta : Angle) return Position is
   begin
      return (x => d * Cos (dCast (theta)), y => d * Sin (dCast (theta)));
   end Create;

   procedure setX (This : in out Position; x : Float) is
   begin
      This.x := x;
   end setX;

   procedure setY (This : in out Position; y : Float) is
   begin
      This.y := y;
   end setY;

   ---------
   -- "+" --
   ---------

   function "+" (This : Position; other : Float) return Position is
   begin
      return Create (norm (This) + other, bearing (This));
   end "+";

   ---------
   -- "-" --
   ---------

   function "-" (This : Position; other : Float) return Position is
   begin
      return Create (norm (This) - other, bearing (This));
   end "-";

   ---------
   -- "+" --
   ---------

   function "+" (This : Position; other : Angle) return Position is
   begin
      return Create (norm (This), bearing (This) + other);
   end "+";

   ---------
   -- "-" --
   ---------

   function "-" (This : Position; other : Angle) return Position is
   begin
      return Create (norm (This), bearing (This) - other);
   end "-";

   ---------
   -- "+" --
   ---------

   function "+" (This : Position; other : Position) return Position is
   begin
      return (x => This.x + other.x, y => This.y + other.y);
   end "+";

   ---------
   -- "-" --
   ---------

   function "-" (This : Position; other : Position) return Position is
   begin
      return (x => This.x - other.x, y => This.y - other.y);
   end "-";

   ---------
   -- "*" --
   ---------

   function "*" (This : Position; scalar : Float) return Position is
   begin
      return (x => This.x * scalar, y => This.y * scalar);
   end "*";

   ---------
   -- "/" --
   ---------

   function "/" (This : Position; scalar : Float) return Position is
   begin
      return (x => This.x / scalar, y => This.y / scalar);
   end "/";

   ---------
   -- "=" --
   ---------

   function "=" (This, Other : Position) return Boolean is
   begin
      return (This.x = Other.x) and then (This.y = Other.y);
   end "=";

   -------------
   -- minimum --
   -------------

   function minimum (This, P : Position) return Position is
   begin
      return (x => Float'Min (This.x, P.x), y => Float'Min (This.y, P.y));
   end minimum;

   -------------
   -- maximum --
   -------------

   function maximum (This, P : Position) return Position is
   begin
      return (x => Float'Max (This.x, P.x), y => Float'Max (This.y, P.y));
   end maximum;

   -------
   -- X --
   -------

   function X (This : Position) return Float is
   begin
      return This.x;
   end X;

   -------
   -- Y --
   -------

   function Y (This : Position) return Float is
   begin
      return This.y;
   end Y;

   ----------
   -- norm --
   ----------

   function norm
     (This : Position)
      return Float
   is
      function Hypot (X, Y : Float) return Float
      with
        Post => Hypot'Result >= 0.0 and then
        (if Hypot'Result > 0.0 then (X /= 0.0 or else Y /= 0.0));
      pragma Import (C, Hypot, "hypotf");
   begin
      return Hypot (This.x, This.y);
   end norm;

   ----------------
   -- squareNorm --
   ----------------

   function squareNorm (This : Position) return Float is
   begin
      return This. x * This. x + This.y * This.y;
   end squareNorm;

   ----------
   -- dist --
   ----------

   function dist (This, Other : Position) return Float is
   begin
      return norm (This - Other);
   end dist;

   -------------
   -- bearing --
   -------------

   function bearing (This : Position) return Angle is
   begin
      return Create (Arctan (This.y, This.x));
   end bearing;

   ------------
   -- scalar --
   ------------

   function scalar (This, P : Position) return Float is
   begin
      return This.x * P.x + This.y * P.y;
   end scalar;

   -----------
   -- print --
   -----------

   function print (This : Position) return String is
   begin
      return "(" & Float'Image (This.x) & ", " & Float'Image (This.x) & ")";
   end print;

end Spaces.Positions;
