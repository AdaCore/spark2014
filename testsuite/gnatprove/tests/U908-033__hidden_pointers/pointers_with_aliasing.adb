with Unchecked_Conversion;
with Unchecked_Deallocation;

package body Pointers_With_Aliasing with SPARK_Mode => Off is
   function Null_Pointer return Pointer is (null);

   function "=" (P1, P2 : Pointer) return Boolean is (Eq (P1, P2));

   function Deref (P : Pointer) return Object is (P.all);

   function Pointer_To_Integer is new
     Unchecked_Conversion (Pointer, Address_Type);
   function Address (P : Pointer) return Address_Type is
     (Pointer_To_Integer (P));

   procedure Assign (P : Pointer; O : Object) is
   begin
      P.all := O;
   end Assign;

   procedure Dealloc_Obj is new Unchecked_Deallocation (Object, Pointer);
   procedure Dealloc (P : in out Pointer) is
   begin
      Dealloc_Obj (P);
   end Dealloc;

   procedure Create (O : Object; P : out Pointer) is
   begin
      P := new Object'(O);
   end Create;

   function Constant_Access (Memory : Memory_Type; P : Pointer) return not null access constant Object is
     (P);

   function Reference (Memory : not null access Memory_Type; P : Pointer) return not null access Object is
     (P);
end Pointers_With_Aliasing;
