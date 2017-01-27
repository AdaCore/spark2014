with Ada.Containers;
with Ada.Containers.Formal_Indefinite_Vectors;
package State_Machine_With_Oop with SPARK_Mode is
   type Root_State is abstract tagged record
      Common_Value : Integer;
   end record;

   function Can_Move_To_A (Current : Root_State) return Boolean is (False);
   function Can_Move_To_B (Current : Root_State) return Boolean is (False);
   function Can_Move_To_C (Current : Root_State) return Boolean is (False);

   function Move_To_A (Current : Root_State) return Root_State'Class is abstract
   with
     Pre'Class => Can_Move_To_A (Current);

   function Move_To_B (Current : Root_State) return Root_State'Class is abstract
   with
     Pre'Class => Can_Move_To_B (Current);

   function Move_To_C (Current : Root_State) return Root_State'Class is abstract
   with
     Pre'Class => Can_Move_To_C (Current);

   procedure Stay_Here (Current : in out Root_State) is abstract
   with
       Pre'Class => not Can_Move_To_A (Current)
                      and then not Can_Move_To_B (Current)
                      and then not Can_Move_To_C (Current);

   type State_A is new Root_State with record
      Value_For_A : Integer;
   end record;

   function Can_Move_To_A (Current : State_A) return Boolean is (False);
   function Can_Move_To_B (Current : State_A) return Boolean is
     (Current.Common_Value >= Current.Value_For_A);
   function Can_Move_To_C (Current : State_A) return Boolean is
     (Current.Common_Value < Current.Value_For_A);

   function Move_To_A (Current : State_A) return Root_State'Class;
   function Move_To_B (Current : State_A) return Root_State'Class;
   function Move_To_C (Current : State_A) return Root_State'Class;
   procedure Stay_Here (Current : in out State_A);

   type State_B is new Root_State with null record;

   function Can_Move_To_A (Current : State_B) return Boolean is (False);
   function Can_Move_To_B (Current : State_B) return Boolean is (False);
   function Can_Move_To_C (Current : State_B) return Boolean is (False);

   function Move_To_A (Current : State_B) return Root_State'Class;
   function Move_To_B (Current : State_B) return Root_State'Class;
   function Move_To_C (Current : State_B) return Root_State'Class;
   procedure Stay_Here (Current : in out State_B);

   function Can_Increase_Value (Current : State_B) return Boolean is
     (Current.Common_Value < Integer'Last);

   type State_C is new Root_State with record
      Value_For_C : Integer;
   end record;

   function Can_Move_To_A (Current : State_C) return Boolean is
     (Current.Common_Value >= Current.Value_For_C);
   function Can_Move_To_B (Current : State_C) return Boolean is (False);
   function Can_Move_To_C (Current : State_C) return Boolean is (False);

   function Move_To_A (Current : State_C) return Root_State'Class;
   function Move_To_B (Current : State_C) return Root_State'Class;
   function Move_To_C (Current : State_C) return Root_State'Class;
   procedure Stay_Here (Current : in out State_C);

   subtype State_Class is Root_State'Class;

   package State_Vectors is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => State_Class,
      Max_Size_In_Storage_Elements => Root_State'Size,
      Bounded      => False);

   procedure Do_Something (States : in out State_Vectors.Vector);
end State_Machine_With_Oop;
