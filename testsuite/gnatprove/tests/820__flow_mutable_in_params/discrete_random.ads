with System.Random_Numbers;

package Discrete_Random with
  SPARK_Mode => On, Always_Terminates
is

   subtype Result_Subtype is Integer range 1 .. 100;

   --  Basic facilities

   type Generator is limited private;

   function Random (Gen : Generator) return Result_Subtype
     with Side_Effects, Global => null;
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

   function Random
     (Gen   : Generator;
      First : Result_Subtype;
      Last  : Result_Subtype) return Result_Subtype
     with Post => Random'Result in First .. Last, Side_Effects, Global => null;
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

   procedure Reset (Gen : Generator; Initiator : Integer);
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

   procedure Reset (Gen : Generator);
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

   --  Advanced facilities

   type State is private;

   procedure Save  (Gen : Generator; To_State   : out State);
   procedure Reset (Gen : Generator; From_State : State);
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

   Max_Image_Width : constant := System.Random_Numbers.Max_Image_Width;

   function Image (Of_State    : State)  return String with Global => null;
   function Value (Coded_State : String) return State with Global => null;

private
   pragma SPARK_Mode (Off);

   type Generator is new System.Random_Numbers.Generator;

   type State is new System.Random_Numbers.State;

end Discrete_Random;
