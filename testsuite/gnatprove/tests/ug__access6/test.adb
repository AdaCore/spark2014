with Ada.Unchecked_Deallocation;
with SPARK.Heap;

procedure Test is
   type Int_Ptr is access Integer;
   type Int_Ptr_Ptr is access Int_Ptr;

   procedure Free is new Ada.Unchecked_Deallocation (Object => Integer, Name => Int_Ptr);

   procedure Free (X : in out Int_Ptr_Ptr) with
     Depends => (SPARK.Heap.Dynamic_Memory => (X, SPARK.Heap.Dynamic_Memory),
                 X => null),
     Post => X = null
   is
      procedure Internal_Free is new Ada.Unchecked_Deallocation
        (Object => Int_Ptr, Name => Int_Ptr_Ptr);
   begin
      if X /= null and then X.all /= null then
         Free (X.all);
      end if;
      Internal_Free (X);
   end Free;

   Y : Int_Ptr     := new Integer'(11);
   Z : Int_Ptr_Ptr := new Int_Ptr'(Y);
begin
   Free (Z);
end Test;
