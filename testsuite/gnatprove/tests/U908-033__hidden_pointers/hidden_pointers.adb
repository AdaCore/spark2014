with Unchecked_Conversion;
with Unchecked_Deallocation;

package body Hidden_Pointers with SPARK_Mode => Off is
   function Null_Pointer return Pointer is (null);

   function "=" (P1, P2 : Pointer) return Boolean is (Eq (P1, P2));

   function Deref (P : Pointer) return Object is (P.all);

   function Pointer_To_Integer is new Unchecked_Conversion (Pointer, Integer_64);
   function Address (P : Pointer) return Integer_64 is
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
end Hidden_Pointers;
