with Ada.Unchecked_Deallocation;

procedure Test with SPARK_Mode is
   type Int_Ptr is access Integer;
   type Int_Ptr_Ptr is access Int_Ptr;

   procedure Free is new Ada.Unchecked_Deallocation (Object => Integer, Name => Int_Ptr);

   procedure Free (X : in out Int_Ptr_Ptr) with
     Depends => (X => null,
                 null => X),
     Post => X = null
   is
      procedure Internal_Free is new Ada.Unchecked_Deallocation
        (Object => Int_Ptr, Name => Int_Ptr_Ptr);
   begin
      if X /= null  then
         declare
            Alias : Int_Ptr := X.all;
         begin
            Free (Alias);
         end;
      end if;
      Internal_Free (X);
   end Free;
begin
   null;
end Test;
