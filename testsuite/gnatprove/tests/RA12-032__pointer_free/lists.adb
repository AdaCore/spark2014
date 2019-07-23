pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

package body Lists is

   procedure Free is new Ada.Unchecked_Deallocation (T, T_Ptr);

   procedure Prepend (List : in out T_Ptr) is
      Head : T_Ptr := new T'(0, List);
   begin
      List := Head;
   end Prepend;

   procedure Remove_Head (List : in out T_Ptr) is
      Next : T_Ptr := List.Next;
   begin
      List := Next;
      Free (Next);
   end Remove_Head;

   procedure Remove_Head_Correct (List : in out T_Ptr) is
      Next : T_Ptr := List.Next;
   begin
      List.Next := null;
      Free (List);
      List := Next;
   end Remove_Head_Correct;

end Lists;
