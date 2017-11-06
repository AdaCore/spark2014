package Classwide with
  SPARK_Mode
is pragma Elaborate_Body;
   type T is tagged record
      Z : Boolean;
      X : Integer;
      Y : Float;
   end record;

   subtype T_Class is T'Class;
   subtype T2_Class is T_Class;

   function Is_Zero (V : T) return Boolean is
      (V.Z = False and then
         V.X = 0 and then
         V.Y = 0.0)
   with
     Global => null;

   function C_Is_Zero (V : T_Class) return Boolean is
      (Is_Zero (V))
   with
     Global => null;

   function D_Is_Zero (V : T) return Boolean is
      (C_Is_Zero (T'Class (V)))
   with
     Global => null,
     Extensions_Visible;

   procedure Init (V : out T) with
     Post => Is_Zero (V),
     Global => null;

   procedure C_Init (V : out T2_Class) with
     Post => C_Is_Zero (V),
     Global => null;

   procedure D_Init (V : out T) with
     Post => D_Is_Zero (V),
     Global => null,
     Extensions_Visible;

   procedure Update (V : in out T) with
     Post => Is_Zero (V),
     Global => null;

   procedure C_Update (V : in out T'Class) with
     Post => C_Is_Zero (V),
     Global => null;

   procedure D_Update (V : in out T) with
     Post => D_Is_Zero (V),
     Global => null,
     Extensions_Visible;

   type U1 is new T with null record;

   function Is_Zero (V : U1) return Boolean is
      (V.Z = False and then
         V.X = 0 and then
         V.Y = 0.0)
   with
     Global => null;

   procedure Init (V : out U1) with
     Post => Is_Zero (V),
     Global => null;

   procedure Update (V : in out U1) with
     Post => Is_Zero (V),
     Global => null;

   subtype U1_Class is U1'Class;

   function C_U1_Is_Zero (V : U1_Class) return Boolean is
      (Is_Zero (V))
   with
     Global => null;

   function D_Is_Zero (V : U1) return Boolean is
      (C_U1_Is_Zero (U1'Class (V)))
   with
     Global => null,
     Extensions_Visible;

   type U2 is new T with record
      W : Integer;
      XX : Integer;
      YY : Float;
   end record;

   function Is_Zero (V : U2) return Boolean is
      (Is_Zero (T(V)) and then
       V.W = 0 and then
         V.XX = 0 and then
         V.YY = 0.0)
   with
     Global => null;

   procedure Init (V : out U2) with
     Post => Is_Zero (V),
     Global => null;

   procedure Update (V : in out U2) with
     Post => Is_Zero (V),
     Global => null;

end Classwide;
