with Ada.Unchecked_Deallocation;
package body Storage with SPARK_Mode is

   function New_Integer (N : Integer) return Weak_Int_Ptr is
      pragma SPARK_Mode (Off);
   begin
      return Weak_Int_Ptr'(Valid => True, Ptr => new Integer'(N));

   exception
      when Storage_Error =>
         return Weak_Int_Ptr'(Valid => False);

   end New_Integer;

   procedure Free (P : in out Weak_Int_Ptr) is

      procedure Local_Free is new Ada.Unchecked_Deallocation
        (Object => Integer, Name => Int_Ptr);

   begin
      if P.Valid then
         Local_Free (P.Ptr);
         P := Weak_Int_Ptr'(Valid => False);
      end if;
   end Free;
end Storage;
