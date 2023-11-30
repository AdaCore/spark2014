with Ada.Unchecked_Conversion;

package Test_External_Variables is
   pragma SPARK_Mode (On);

   type Normal_Rec is record
      Comp : Integer;
   end record;

   type Volatile_Int is new Integer range 1 .. 1000 with Volatile;

   type Mixed_Rec is record
      Comp : Volatile_Int;
   end record;

   type Volatile_Rec is record
      Comp : Volatile_Int;
   end record with Volatile;

   --  A non-volatile object shall not have a Volatile component

   OK_1    : Normal_Rec;
   OK_2    : Volatile_Int;
   OK_3    : Volatile_Rec;
   OK_4    : Integer      with Volatile;
   OK_5    : Normal_Rec   with Volatile;
   OK_6    : Volatile_Int with Volatile;
   OK_7    : Volatile_Rec with Volatile;
   OK_8    : Mixed_Rec    with Volatile;
   Error_1 : Mixed_Rec;

   --  A constant, a discriminant or a loop parameter shall not be Volatile

   OK_9    : constant Normal_Rec   := (Comp => 123);
   Error_2 : constant Volatile_Int := 456;
   Error_3 : constant Volatile_Rec := (Comp => 789);
   Error_4 : constant Integer      with Volatile, Import;
   Error_5 : constant Normal_Rec   with Volatile, Import;
   Error_6 : constant Volatile_Int with Volatile, Import;
   Error_7 : constant Volatile_Rec with Volatile, Import;
   Error_8 : constant Mixed_Rec    with Volatile, Import;

   type Error_Typ_1 (Error_Disc : Volatile_Int) is null record;

   --  If a Volatile object has Effective_Reads set to True then it must have a
   --  mode_selector of Output or In_Out when denoted as a global_item.

   Item : Integer with Volatile, Async_Writers, Effective_Reads;

   procedure Error_Proc_1 with Global => (Input  => Item);
   procedure OK_Proc_1    with Global => (In_Out => Item);
   procedure OK_Proc_2    with Global => (Output => Item);

   --  A Volatile object shall only occur as an actual parameter of a
   --  subprogram if the corresponding formal parameter is of a non-scalar
   --  Volatile type or as an actual parameter in a call to an instance of
   --  Unchecked_Conversion.

   type Non_Volatile_Int is new Integer range 1 .. 1000;

   OK_10 : Non_Volatile_Int with Volatile;

   function To_Integer is
     new Ada.Unchecked_Conversion (Non_Volatile_Int, Integer);

   OK_11 : Integer := To_Integer (OK_10);
end Test_External_Variables;
