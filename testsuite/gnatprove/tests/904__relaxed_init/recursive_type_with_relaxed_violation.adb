procedure Recursive_Type_With_Relaxed_Violation with SPARK_Mode is
   type My_Int is new Integer with Relaxed_Initialization;
   type R;
   type R_Access is access R;
   type U (P : Boolean := True) is record
      case P is
      when True =>
         A : R_Access;
      when False =>
         null;
      end case;
   end record with Unchecked_Union;
   type R is record
      F : U;
      G : My_Int;
   end record;
begin
   null;
end;
