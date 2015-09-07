pragma SPARK_Mode(On);
with Double_List;  -- The generic doubly-linked list package
pragma Elaborate_All(Double_List);
package body List_Handler
   with
      Refined_State => (List => Integer_List.Internal_List)
is
   package Integer_List is new Double_List (Element_Type    => Integer,
                                            Max_Size        => 128,
                                            Default_Element => 0);
   use type Integer_List.Status_Type;

   procedure Append_Range(Lower, Upper : in Integer)
      with
         Refined_Global  => (In_Out => Integer_List.Internal_List),
         Refined_Depends => (Integer_List.Internal_List =>+ (Lower, Upper))
   is
      Current : Integer := Lower;
      Status  : Integer_List.Status_Type;
   begin
      while Current <= Upper loop
         Integer_List.Insert_Before (It     => Integer_List.Back,
                                     Item   => Current,
                                     Status => Status);
         exit when Status /= Integer_List.Success or Current = Upper;
         Current := Current + 1;
      end loop;
   end Append_Range;
end List_Handler;
