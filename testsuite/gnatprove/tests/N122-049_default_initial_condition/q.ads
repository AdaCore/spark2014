with Types;
package Q
  with SPARK_Mode => On
is
   --  More test cases for Default_Initial_Condition
   --  on private types.

   type T1 is private
     with Default_Initial_Condition;

   type T2 is private
     with Default_Initial_Condition;

   type T3 is private
     with Default_Initial_Condition;

   type T4 is private
     with Default_Initial_Condition;

   type T5 is private
     with Default_Initial_Condition;

   type T6 is private
     with Default_Initial_Condition;

   type T7 is private
     with Default_Initial_Condition;

   type T8 is private
     with Default_Initial_Condition;

   type T9 is private
     with Default_Initial_Condition;

private

   type T1 is range 1 .. 10; -- error

   type T2 is range 1 .. 20
     with Default_Value => 4; -- OK

   type T3 is array (T2) of Integer; -- error

   type T4 is array (T2) of Integer
     with Default_Component_Value => 5; -- OK

   type T5 is record -- error
      F1 : Types.S2;     -- OK
      F2 : Types.Colour; -- OK
      F3 : Types.S1;     -- No default...
   end record;

   type T6 is record -- OK
      F1 : Types.S2;     -- OK
      F2 : Types.Colour; -- OK
   end record;

   -- Derived types
   type T7 is new Types.S2; -- OK???

   type T8 is new Types.FR; -- OK???

   type T9 is new Types.AR; -- OK???

end Q;
