package State_Machine_With_Discriminant with SPARK_Mode is
   type State_Kind is (A, B, C);
   type State (Kind : State_Kind := A) is record
      Common_Value : Integer;
      case Kind is
         when A => Value_For_A : Integer;
         when B => null;
         when C => Value_For_C : Integer;
      end case;
   end record;

   function Can_Move_To_A (Current : State) return Boolean is
     (Current.Kind = C);
   function Can_Move_To_B (Current : State) return Boolean is
     (Current.Kind = A);
   function Can_Move_To_C (Current : State) return Boolean is
     (Current.Kind = A);

   function Can_Increase_Value (Current : State) return Boolean is
     (Current.Common_Value < Integer'Last)
   with
     Pre => Current.Kind = B;

   procedure Move_To_A (Current : in out State) with
     Pre  => Can_Move_To_A (Current) and then not Current'Constrained,
     Post => Current.Kind = A;

   procedure Move_To_B (Current : in out State) with
     Pre  => Can_Move_To_B (Current) and then not Current'Constrained,
     Post => Current.Kind = B;

   procedure Move_To_C (Current : in out State) with
     Pre  => Can_Move_To_C (Current) and then not Current'Constrained,
     Post => Current.Kind = C;

   procedure Stay_Here (Current : in out State) with
     Pre  => not Can_Move_To_A (Current)
             and then not Can_Move_To_B (Current)
             and then not Can_Move_To_C (Current),
     Post => Current.Kind = Current.Kind'Old;

   type State_Array is array (Positive range <>) of State;

   procedure Do_Something (States : in out State_Array);
end State_Machine_With_Discriminant;
