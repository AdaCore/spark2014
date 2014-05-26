
with Formal.Numerics.Elementary_Functions;
use Formal.Numerics.Elementary_Functions;

package body Spaces.Poses is

   ------------
   -- Create --
   ------------

   function Create (X, Y : Float; Theta : Angle) return Pose is
   begin
      return (pos => Create (X, Y), ori => Theta);
   end Create;

   ------------
   -- Create --
   ------------

   function Create (pos : Position; ori : Angle) return Pose is
   begin
      return (pos => pos, ori => ori);
   end Create;

   ---------
   -- "+" --
   ---------

   function "+" (This, Other : Pose) return Pose is
   begin
      return (pos => This.pos + Other.pos, ori => This.ori + Other.ori);
   end "+";

   ---------
   -- "-" --
   ---------

   function "-" (This, Other : Pose) return Pose is
   begin
      return (pos => This.pos - Other.pos, ori => This.ori - Other.ori);
   end "-";

   ---------
   -- "*" --
   ---------

   function "*" (This : Pose; P : Position) return Position is
    x : constant Float := Spaces.Positions.X (P) *  Cos (dCast (This.ori)) - Spaces.Positions.Y (P) * Sin (dCast (This.ori)) + Spaces.Positions.X (This.pos);
    y : constant Float := Spaces.Positions.X (P) *  Sin (dCast (This.ori)) + Spaces.Positions.Y (P) * Cos (dCast (This.ori)) + Spaces.Positions.Y (This.pos);
   begin
      return Create (x, y);
   end "*";

   ---------
   -- "=" --
   ---------

   function "=" (This, Other : Pose) return Boolean is
   begin
      return (This.pos = Other.pos) and then (This.ori = Other.ori);
   end "=";

   ---------
   -- pos --
   ---------

   function pos (This : Pose) return Position is
   begin
      return This.pos;
   end pos;

   ---------
   -- ori --
   ---------

   function ori (This : Pose) return Angle is
   begin
      return This.ori;
   end ori;

   ----------
   -- setX --
   ----------

   procedure setX (This : in out Pose; X : Float) is
   begin
      setX (This.pos, X);
   end setX;

   ----------
   -- setY --
   ----------

   procedure setY (This : in out Pose; Y : Float) is
   begin
      setY (This.pos, Y);
   end setY;

   ------------
   -- setOri --
   ------------

   procedure setOri (This : in out Pose; ori : Angle) is
   begin
      This.ori := ori;
   end setOri;

   -----------
   -- print --
   -----------

   function print (This : Pose) return String is
   begin
      return "(" &  print (This.pos) & ", " & Print (This.ori) & ")";
   end print;

end Spaces.Poses;
