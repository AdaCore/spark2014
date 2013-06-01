package body Array_Aggregates
is
   type Small_Index_T is range 1..1000;
   type Length_T is range 0..5;
   subtype Index_T is Length_T range 1..Length_T'Last;
   type String_Body_T is array (Index_T) of Character;

   type String_T is record
      Len  : Length_T;
      Elem : String_Body_T;
   end record;

   type Int_String_T_Array is array (Small_Index_T) of String_T;

   procedure Aggregate_Test_AI (X : out Int_String_T_Array)
    with Depends => (X => null)
   is
   begin
      X := Int_String_T_Array'(others => String_T'(Len => 0,
                                                   Elem => String_Body_T'(others => ' ')));
      pragma Assert (for all N in Small_Index_T => (X (N) = String_T'(Len => 0,
                                                                      Elem => String_Body_T'(others => ' '))));
   end Aggregate_Test_AI;
end Array_Aggregates;
