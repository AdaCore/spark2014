package body Allocator.Base.Ownership_Wrapper
  with SPARK_Mode => Off
is

   use Memory_Index_Sequences;

   function Num_Free return Big_Natural
   is (Length (Free_Cells));

   function Is_Full return Boolean
   is (Free = 0);

   function Deref (P : Object_Pointer) return Binary_Object_Type is
   begin
      return Deref (P.Index);
   end Deref;

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Binary_Object_Type
   is
      O : aliased Binary_Object_Type
      with Import, Address => Memory (P.Index)'Address;
   begin
      return O'Unchecked_Access;
   end Constant_Reference;

   function Reference
     (P : in out Object_Pointer) return not null access Binary_Object_Type
   is
      O : aliased Binary_Object_Type
      with Import, Address => Memory (P.Index)'Address;
   begin
      return O'Unchecked_Access;
   end Reference;

   function Allocate (O : Binary_Object_Type) return Object_Pointer is
      Base_O : constant Binary_Object_Type
      with Import, Address => O'Address;
   begin
      return (Index => Allocate (Base_O));
   end Allocate;

   procedure Deallocate (P : in out Object_Pointer) is
   begin
      if P.Index /= 0 then
         Deallocate (P.Index);
         P.Index := 0;
      end if;
   end Deallocate;

end Allocator.Base.Ownership_Wrapper;
